class LTLDAG:
    """
    _nodes : list of (op, left, right)
    _index : dict (op, left, right) -> node id
    """

    def __init__(self):
        self._nodes = [
            ('false', None, None),
            ('true', None, None),
        ]
        self._index = {
            ('false', None, None): 0,
            ('true', None, None): 1,
        }

        self.make_reduce = self.make

    def make(self, op, left=None, right=None):
        left = self._resolve(left)
        right = self._resolve(right)

        key = (op, left, right)
        if key in self._index:
            return self._index[key]

        nid = len(self._nodes)
        self._nodes.append(key)
        self._index[key] = nid
        return nid

    def _resolve(self, x):
        if x is None or isinstance(x, int):
            return x
        if isinstance(x, tuple):
            if len(x) == 2:
                return self.make(x[0], x[1])
            if len(x) == 3:
                return self.make(x[0], x[1], x[2])
        raise ValueError(f"Cannot resolve node reference: {x}")

    def to_str(self, nid):
        op, left, right = self._nodes[nid]

        if left is None:
            return op

        if right is None:
            return f"{op} {self.to_str(left)}"

        return f"{op} {self.to_str(left)} {self.to_str(right)}"

    def to_infix(self, nid):
        op, left, right = self._nodes[nid]

        # atoms / constants
        if left is None:
            return op

        # unary
        if right is None:
            sub = self.to_infix(left)
            if op in ('~', '!'):
                return f"!{sub}" if len(sub) == 1 else f"!({sub})"
            return f"{op}({sub})"

        # binary:
        l = self.to_infix(left)
        r = self.to_infix(right)
        return f"({l} {op} {r})"


class LTLDAGNode(object):
    """
    A lightweight wrapper that couples a raw integer node ID
    with its parent DAG context so parsing methods can stay object-oriented.
    """
    def __init__(self, dag, node_id):
        self.dag = dag
        self.node_id = node_id

    def __repr__(self):
        return f"LTLDAGNode({self.node_id})"


def to_pnf(dag, nid, neg=False):
    op, left, right = dag._nodes[nid]
    # constants (true, false, atoms)
    if left is None:
        if op == 'true':
            return dag._index[('false', None, None)] if neg else dag._index[('true', None, None)]
        if op == 'false':
            return dag._index[('true', None, None)] if neg else dag._index[('false', None, None)]
        return dag.make('~', nid) if neg else nid

    # negation
    if op in ('~', '!'):
        return to_pnf(dag, left, not neg)

    # F, I expand it into U and R immediately
    if op == 'F':
        child = to_pnf(dag, left, neg)
        if not neg:
            # F negated becomes U
            return dag.make('U', dag._index[('true', None, None)], child)
        else:
            # Normal F becomes R
            return dag.make('R', dag._index[('false', None, None)], child)

    # Same for G, expended immediately into R and U
    if op == 'G':

        child = to_pnf(dag, left, neg)
        if not neg:
            return dag.make('R', dag._index[('false', None, None)], child)
        else:
            return dag.make('U', dag._index[('true', None, None)], child)

    # X
    if op == 'X':
        return dag.make('X', to_pnf(dag, left, neg))

    # all operators with left and right:
    l = to_pnf(dag, left, neg)
    r = to_pnf(dag, right, neg)
    if op == 'U':
        return dag.make('R', l, r) if neg else dag.make('U', l, r)

    if op == 'R':
        return dag.make('U', l, r) if neg else dag.make('R', l, r)

    if op == '&':
        return dag.make('|', l, r) if neg else dag.make('&', l, r)

    if op == '|':
        return dag.make('&', l, r) if neg else dag.make('|', l, r)

    if op == 'W':
        if not neg:
            return dag.make('R', r, dag.make('|', l, r))
        else:
            return dag.make('U', r, dag.make('&', l, r))

    if op == 'M':
        if not neg:
            return dag.make('U', r, dag.make('&', l, r))
        else:
            return dag.make('R', r, dag.make('|', l, r))

    raise ValueError(f"Unknown operator in to_pnf: {op}")

