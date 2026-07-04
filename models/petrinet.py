# !/usr/bin/python3
# -*- coding_ utf-8 -*-

from array import array
from collections import Counter
from typing import Dict, Text, List
from lxml import etree

from part1.models.NBA import get_nba_successors_lazy
from part1.models.ltl_model import LTLDAG, LTLDAGNode


class PetriNetModel(object):
    def __init__(self, places, transitions, p_ids, t_ids, tin, tout, initial):
        self.places = places
        self.transitions = transitions
        self.p_ids = p_ids
        self.t_ids = t_ids
        self.tin = [Counter(x) for x in tin]
        self.tout = [Counter(x) for x in tout]
        self.initial = tuple(initial)

    def initial_states(self):
        yield self.initial

    def successors(self, marking):
        for i in range(len(self.tin)):
            if self.is_enabled(i, marking):
                new_marking = array('I', marking)
                for x, y in self.tin[i].items():
                    new_marking[x] -= y
                for x, y in self.tout[i].items():
                    new_marking[x] += y
                yield self.transitions[i], tuple(new_marking)

    def is_enabled(self, transition, marking):
        for x, y in self.tin[transition].items():
            if marking[x] < y:
                return False
        return True


def parse_pnml_file(path):
    parser = etree.XMLParser(remove_comments=True, ns_clean=True)
    tree = etree.parse(path, parser=parser)

    # Strip annoying namespace tags
    for elem in tree.getiterator():
        elem.tag = etree.QName(elem).localname
    etree.cleanup_namespaces(tree)

    root = tree.getroot()
    nets = []  # list for parsed PetriNet objects

    for net_node in root.iter('net'):
        # parse transitions
        transitions = [t.get('id') for t in net_node.iter('transition')]
        t_ids = {x: i for i, x in enumerate(transitions)}

        # parse places
        places = []
        p_ids: Dict[Text, int] = {}
        initial = []
        for i, p in enumerate(net_node.iter('place')):
            places.append(p.get('id'))
            p_ids[p.get('id')] = i
            place_initial = 0
            for child in p:
                if "initialMarking" in child.tag:
                    for child2 in child:
                        if child2.tag == "text":
                            place_initial = int(child2.text)
            initial.append(place_initial)

        initial = array('I', initial)
        transitions_in: List[List[int]] = [[] for _ in t_ids]
        transitions_out: List[List[int]] = [[] for _ in t_ids]

        # parse arcs
        for arc_node in net_node.iter('arc'):
            source: Text = arc_node.get('source')
            target: Text = arc_node.get('target')
            if source in p_ids and target in t_ids:
                transitions_in[t_ids[target]].append(p_ids[source])
            elif source in t_ids and target in p_ids:
                transitions_out[t_ids[source]].append(p_ids[target])

        # create PetriNet object
        nets.append(PetriNetModel(places, transitions, p_ids, t_ids, transitions_in, transitions_out, initial))

    return nets


class PNExpression(object):
    def evaluate(self, _):
        pass


class IsFireable(PNExpression):
    def __init__(self, net, *args):
        self.net = net
        self.transitions = args

    def evaluate(self, marking):
        for t in self.transitions:
            if self.net.is_enabled(t, marking):
                return True
        return False

    def __repr__(self):
        return "is-fireable({})".format(self.transitions)


class TokensCount(PNExpression):
    def __init__(self, net, *args):
        self.net = net
        self.places = args

    def evaluate(self, marking):
        return sum([marking[p] for p in self.places])

    def __repr__(self):
        return "tokens-count({})".format(self.places)


class IntegerLE(PNExpression):
    def __init__(self, net, lhs, rhs):
        self.net = net
        self.lhs = lhs
        self.rhs = rhs

    def evaluate(self, marking):
        return self.lhs.evaluate(marking) <= self.rhs.evaluate(marking)

    def __repr__(self):
        return "{} <= {}".format(self.lhs, self.rhs)


class IntegerConstant(PNExpression):
    def __init__(self, net, value):
        self.net = net
        self.value = value

    def evaluate(self, marking):
        return self.value

    def __repr__(self):
        return str(self.value)


class IntegerSum(PNExpression):
    def __init__(self, net, *args):
        self.net = net
        self.subexpressions = args

    def evaluate(self, marking):
        return sum([x.evaluate(marking) for x in self.subexpressions])

    def __repr__(self):
        return " + ".join(self.subexpressions)


class IntegerDifference(PNExpression):
    def __init__(self, net, lhs, rhs):
        self.net = net
        self.lhs = lhs
        self.rhs = rhs

    def evaluate(self, marking):
        return self.lhs.evaluate(marking) - self.rhs.evaluate(marking)

    def __repr__(self):
        return "{} - {}".format(self.lhs, self.rhs)


class PropertyXMLParser(object):
    def __init__(self, net):
        self.props = []
        self.dag = LTLDAG()
        self.net = net

    def __call__(self, node):
        return self.props, LTLDAGNode(self.dag, self.parse_ltl(node))

    def parse_ltl(self, node):
        """Dedicated parser for logical LTL formulas. ALWAYS returns an integer node ID."""
        tag = node.tag
        if tag == 'formula' or tag == 'all-paths':
            return self.parse_ltl(node.getchildren()[0])

        # MCC uses 'negation' instead of 'not'
        elif tag in ('negation', 'not'):
            sub = self.parse_ltl(node.getchildren()[0])
            return self.dag.make_reduce('~', sub)

        # MCC uses 'conjunction' instead of 'and'
        elif tag in ('conjunction', 'and'):
            subs = [self.parse_ltl(x) for x in node.getchildren()]
            res = subs[0]
            for s in subs[1:]:
                res = self.dag.make_reduce('&', res, s)
            return res

        # MCC uses 'disjunction' instead of 'or'
        elif tag in ('disjunction', 'or'):
            subs = [self.parse_ltl(x) for x in node.getchildren()]
            res = subs[0]
            for s in subs[1:]:
                res = self.dag.make_reduce('|', res, s)
            return res

        elif tag == 'globally':
            sub = self.parse_ltl(node.getchildren()[0])
            return self.dag.make_reduce('G', sub)
        elif tag == 'finally':
            sub = self.parse_ltl(node.getchildren()[0])
            return self.dag.make_reduce('F', sub)
        elif tag == 'until':
            lhs = self.parse_ltl(next(node.iterchildren('before')).getchildren()[0])
            rhs = self.parse_ltl(next(node.iterchildren('reach')).getchildren()[0])
            return self.dag.make_reduce('U', lhs, rhs)
        elif tag == 'next':
            sub = self.parse_ltl(node.getchildren()[0])
            return self.dag.make_reduce('X', sub)
        elif tag == 'is-fireable':
            subs = tuple(self.net.t_ids[x.text] for x in node.getchildren() if x.tag == 'transition')
            p = IsFireable(self.net, *subs)
            self.props.append(p)
            return self.dag.make('p' + str(len(self.props) - 1))
        elif tag == 'integer-le':
            lhs = self.parse_numeric(node.getchildren()[0])
            rhs = self.parse_numeric(node.getchildren()[1])
            p = IntegerLE(self.net, lhs, rhs)
            self.props.append(p)
            return self.dag.make('p' + str(len(self.props) - 1))

        raise ValueError(f"Unknown logical LTL tag: {tag}")

    def parse_numeric(self, node):
        """Dedicated parser for numeric expressions. ALWAYS returns a PNExpression object."""
        tag = node.tag
        if tag == 'integer-constant':
            return IntegerConstant(self.net, int(node.text))
        elif tag == 'integer-sum':
            subs = [self.parse_numeric(x) for x in node.getchildren()]
            return IntegerSum(self.net, *subs)
        elif tag == 'integer-difference':
            lhs = self.parse_numeric(node.getchildren()[0])
            rhs = self.parse_numeric(node.getchildren()[1])
            return IntegerDifference(self.net, lhs, rhs)
        elif tag == 'tokens-count':
            subs = tuple(self.net.p_ids[x.text] for x in node.getchildren() if x.tag == 'place')
            return TokensCount(self.net, *subs)

        raise ValueError(f"Unknown mathematical numeric tag: {tag}")


def parse_property_xml(net, path):
    parser = etree.XMLParser(remove_comments=True, ns_clean=True)
    tree = etree.parse(path, parser=parser)

    for elem in tree.getiterator():
        elem.tag = etree.QName(elem).localname
    etree.cleanup_namespaces(tree)

    root = tree.getroot()
    props = []

    for prop_node in root.iter('property'):
        prop_id = ''
        prop = None
        for child in prop_node.getchildren():
            if child.tag == 'id':
                prop_id = child.text
            if child.tag == 'formula':
                prop = PropertyXMLParser(net)(child)
        if prop is not None:
            props.append((prop_id, prop[0], prop[1]))
    return props


def get_petri_product_successors_lazy(net, props_list):
    """
    Synchronized product space successor generator.
    This gets used as a successor function in dfs.
    """
    # Cache node_id -> atomic string mapping.
    # This turns an O(N) DAG list-unpacker into a O(1) dictionary hit.
    atomic_cache = {}

    def generator(dag, v, closure, gnba_acc_sets, k):
        marking, (nba_formulas, layer) = v

        # 1. Evaluate what are true atomic propositions for the current marking
        true_atoms = set()
        for idx, prop_expr in enumerate(props_list):
            if prop_expr.evaluate(marking):
                true_atoms.add(f"p{idx}")

        # 2. Extract expected APs from the NBA state using the cache
        nba_expected_atoms = set()
        for node_id in nba_formulas:
            if node_id not in atomic_cache:
                node_tag = dag._nodes[node_id][0]
                if isinstance(node_tag, str) and node_tag.startswith('p'):
                    atomic_cache[node_id] = node_tag
                else:
                    atomic_cache[node_id] = None

            tag = atomic_cache[node_id]
            if tag:
                nba_expected_atoms.add(tag)

        # 3. Guard: If current marking doesn't satisfy the current NBA node requirements,
        # stop immediately before evaluating any physical petri net transitions
        if not nba_expected_atoms.issubset(true_atoms):
            return

        # 4. Transitions only fire if the LTL guard conditions pass
        for _, next_marking in net.successors(marking):
            nba_state = (nba_formulas, layer)
            for _, next_nba in get_nba_successors_lazy(dag, nba_state, closure, gnba_acc_sets, k):
                yield None, (next_marking, next_nba)

    return generator
