def compute_closure(dag, root):
    """Computes the closure of a ltl formula by starting at the root and visiting sub-formula's"""
    closure = set()

    def visit(nid):
        op, left, right = dag._nodes[nid]

        # ignore the negated version
        if op in ('~', '!'):
            visit(left)
            return

        if nid in closure:
            return
        closure.add(nid)

        if left is not None:  visit(left)
        if right is not None: visit(right)

    visit(root)
    return closure


def generate_consistent_states(dag, closure):
    """
    Generator that yields consistent states. We use generator so we do not have to store 2^n state at once.
    """
    closure_list = sorted(closure)
    n = len(closure_list)

    for mask in range(1 << n):   # 0 to 2^n - 1
        subset = frozenset(closure_list[i] for i in range(n) if (mask >> i) & 1)  # powerset of closure
        if is_consistent(dag, subset, closure):
            yield subset


def is_consistent(dag, subset, closure):
    """Checks if a subset of formula's is consistent with the closure"""
    nodes = dag._nodes
    TRUE = dag._index[('true', None, None)]
    FALSE = dag._index[('false', None, None)]

    # Cache to prevent deep redundant tree traversal recursion
    cache = {}

    def eval_node(nid):
        if nid in cache:
            return cache[nid]

        if nid == TRUE: return True
        if nid == FALSE: return False

        op, l, r = nodes[nid]
        if l is None:  # Atomic Proposition
            res = nid in subset
            cache[nid] = res
            return res

        if op in ('~', '!'):
            res = not eval_node(l)
        elif op == '&':
            res = eval_node(l) and eval_node(r)
        elif op == '|':
            res = eval_node(l) or eval_node(r)
        elif op == 'U':
            if nid not in subset and eval_node(r):
                res = False
            elif nid in subset and not (eval_node(l) or eval_node(r)):
                res = False
            else:
                res = nid in subset
        elif op == 'R':
            if nid not in subset and (eval_node(l) and eval_node(r)):
                res = False
            elif nid in subset and not eval_node(r):
                res = False
            else:
                res = nid in subset
        elif op == 'X':
            res = nid in subset
        else:
            res = False

        cache[nid] = res
        return res

    # 1. Constant constraints
    if TRUE in closure and TRUE not in subset:
        return False
    if FALSE in subset:
        return False

    # 2. Structural/Semantic constraints
    for nid in closure:
        op, l, r = nodes[nid]

        if not eval_node(nid) and nid in subset:
            return False

        if op == '&' and eval_node(l) and eval_node(r) and nid not in subset:
            return False
        if op == '|' and (eval_node(l) or eval_node(r)) and nid not in subset:
            return False
        if op == 'U' and eval_node(r) and nid not in subset:
            return False

    return True


def get_gnba_successors_lazy(dag, current_state, closure):
    """
    Highly optimized, truly lazy GNBA successor generator.
    Derives next-state properties directly from the current state rules.
    """
    nodes = dag._nodes
    closure_list = sorted(closure)

    # 1. Deduce absolute requirements for the candidate successor state
    must_have = set()
    must_not_have = set()

    for nid in closure:
        op, l, r = nodes[nid]

        if op == 'X':
            # Next-step rule: X(l) in current_state <=> l MUST be in next state
            if nid in current_state:
                must_have.add(l)
            else:
                must_not_have.add(l)

        elif op == 'U':
            u_in_now = nid in current_state
            r_in_now = r in current_state
            # Step rule for Until: if u is true now but r isn't satisfied yet,
            # then u MUST persist into the next state.
            if u_in_now and not r_in_now:
                must_have.add(nid)
            # If u is false now, it cannot be true in the next state unless r is met now
            elif not u_in_now:
                must_not_have.add(nid)

    # Quick check: If an element is simultaneously forced to be true and false, exit early
    if not must_have.isdisjoint(must_not_have):
        return

    # 2. Backtrack and branch ONLY over the remaining unconstrained nodes in the closure
    unconstrained = [nid for nid in closure_list if nid not in must_have and nid not in must_not_have]

    def branch_successors(index, current_built_set):
        if index == len(unconstrained):
            candidate = frozenset(current_built_set)
            # Check semantic/boolean consistency of this specific candidate state on-the-fly
            if is_consistent(dag, candidate, closure):
                lbl = get_label(dag, candidate)
                yield lbl, candidate
            return

        nid = unconstrained[index]

        # Branch 1: Try adding the subformula to the next state
        current_built_set.add(nid)
        yield from branch_successors(index + 1, current_built_set)
        current_built_set.remove(nid)

        # Branch 2: Try leaving it out of the next state
        yield from branch_successors(index + 1, current_built_set)

    # Begin the localized, bounded search
    starting_set = set(must_have)
    yield from branch_successors(0, starting_set)


def get_label(dag, state):
    """returns the true atomic propositions from the dag representation"""
    nodes = dag._nodes
    true_aps = set()

    for nid in state:
        op, l, r = nodes[nid]
        if l is None and op not in ('true', 'false'):
            true_aps.add(op)

    return frozenset(true_aps)


def is_valid_successor(dag, state, state2, closure):
    """computes if state2 is a valid successor of the current state"""
    nodes = dag._nodes

    for nid in closure:
        op, l, r = nodes[nid]

        if op == 'X':
            x_in_now = nid in state
            l_in_next = l in state2
            if x_in_now != l_in_next:
                return False

        elif op == 'U':
            u_in_now = nid in state
            r_in_now = r in state
            l_in_now = l in state
            u_in_next = nid in state2

            expected_u_now = r_in_now or (l_in_now and u_in_next)
            if u_in_now != expected_u_now:
                return False

        elif op == 'R':
            r_in_now = nid in state
            l_in_now = l in state
            right_formula_in_now = r in state
            r_in_next = nid in state2

            expected_r_now = (l_in_now and right_formula_in_now) or (right_formula_in_now and r_in_next)
            if r_in_now != expected_r_now:
                return False

    return True


def compute_acceptance(dag, states, closure):
    """computes the acceptance set(s)"""
    nodes = dag._nodes
    acceptance = []

    for nid in sorted(closure):
        op, l, r = nodes[nid]
        if op == 'U':
            acc = frozenset(
                s for s in states
                if nid not in s or r in s
            )
            acceptance.append(acc)

    if not acceptance:
        acceptance.append(frozenset(states))

    return acceptance


class GNBA:
    def __init__(self, states, initial, transitions, acceptance, ap_names):
        self.states = states
        self.initial = initial
        self.transitions = transitions
        self.acceptance = acceptance
        self.ap_names = ap_names


def build_gnba(dag, root):
    # 1. closure
    closure = compute_closure(dag, root)

    # 2. consistent states
    states = list(generate_consistent_states(dag, closure))
    if not states:
        raise ValueError("No consistent states — formula may be unsatisfiable.")

    # 3. initial states
    initial = [i for i, s in enumerate(states) if root in s]

    # 4. AP names
    d = dag._nodes
    ap_names = sorted({
        op
        for nid in closure
        for (op, l, r) in [d[nid]]
        if l is None and op not in ('true', 'false')
    })

    # 5. transitions
    transitions = {i: [] for i in range(len(states))}
    for i, s in enumerate(states):
        lbl = get_label(dag, s)
        for j, s2 in enumerate(states):
            if is_valid_successor(dag, s, s2, closure):
                transitions[i].append((lbl, j))

    # 6. acceptance sets
    acceptance = compute_acceptance(dag, states, closure)

    gnba = GNBA(states, initial, transitions, acceptance, ap_names)

    return gnba


# =========================================================
# HOA OUTPUT & DOT UTILITIES
# =========================================================

def label_to_hoa(true_aps, ap_names):
    if not ap_names:
        return "t"
    return " & ".join(ap if ap in true_aps else f"!{ap}" for ap in ap_names)


def to_dot(gnba: GNBA, dag=None, formula_str=""):
    acc_sets = gnba.acceptance
    n_acc = len(acc_sets)

    def acceptance_rank(state_content):
        return sum(1 for acc in acc_sets if state_content in acc)

    lines = []
    lines.append("digraph GNBA {")
    lines.append('  rankdir=LR;')
    lines.append('  node [shape=circle, fontname="Helvetica"];')
    if formula_str:
        lines.append(
            f'  label={_dot_quote("GNBA: " + formula_str)};')
        lines.append('  labelloc=t;')
    lines.append("")

    for i in gnba.initial:
        lines.append(f'  __init_{i} [shape=point, style=invis, width=0];')

    lines.append("")

    for i in range(len(gnba.states)):
        actual_state = gnba.states[i]
        rank = acceptance_rank(actual_state)

        if rank == n_acc:
            shape_attr = 'shape=doublecircle'
        elif rank > 0:
            shape_attr = 'shape=circle, style=bold'
        else:
            shape_attr = 'shape=circle'

        if n_acc > 1 and rank > 0:
            acc_label = "{" + ",".join(str(k) for k, acc in enumerate(acc_sets) if i in acc) + "}"
            label = f'S{i}\\n{acc_label}'
        else:
            label = f'S{i}'

        is_init = i in gnba.initial
        if is_init:
            extra = ', style=filled, fillcolor=lightblue'
        else:
            extra = ''

        lines.append(f'  {i} [label={_dot_quote(label)}, {shape_attr}{extra}];')

    lines.append("")

    for i in gnba.initial:
        lines.append(f'  __init_{i} -> {i};')

    lines.append("")

    edge_labels = {}
    for i, trans in gnba.transitions.items():
        for lbl, j in trans:
            lbl_str = label_to_hoa(lbl, gnba.ap_names)
            edge_labels.setdefault((i, j), []).append(lbl_str)

    for (i, j), labels in sorted(edge_labels.items()):
        unique = list(dict.fromkeys(labels))
        combined = "\\n".join(unique)
        lines.append(f'  {i} -> {j} [label={_dot_quote(combined)}];')

    if dag is not None:
        lines.append("")
        lines.append("  subgraph cluster_legend {")
        lines.append('    label="Legend"; fontname="Helvetica"; style=dashed;')
        lines.append('    node [shape=none, margin=0];')
        lines.append('    legend [label=<')
        lines.append('      <TABLE BORDER="0" CELLBORDER="1" CELLSPACING="0" CELLPADDING="4">')
        lines.append('        <TR><TD><B>State</B></TD><TD><B>Contents</B></TD></TR>')
        for i, s in enumerate(gnba.states):
            contents = ", ".join(dag.to_infix(n) for n in sorted(s))
            if not contents:
                contents = "{}"
            si = _dot_html_escape(f"S{i}")
            cont = _dot_html_escape("{ " + contents + " }")
            lines.append(f'        <TR><TD ALIGN="LEFT">{si}</TD><TD ALIGN="LEFT">{cont}</TD></TR>')
        lines.append('      </TABLE>>];')
        lines.append("  }")

    lines.append("}")
    return "\n".join(lines)


def _dot_html_escape(s):
    return s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def _dot_quote(s):
    return '"' + s.replace('"', '\\"') + '"'


def print_gnba_transitions(gnba: GNBA):
    print("\nTransitions:")
    for src_state, transitions in gnba.transitions.items():
        if not transitions:
            print(f"  S{src_state} -> (no outgoing transitions)")
            continue

        for lbl, dst_state in transitions:
            lbl_str = label_to_hoa(lbl, gnba.ap_names)
            print(f"  S{src_state} --[{lbl_str}]--> S{dst_state}")
