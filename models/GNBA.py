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


def evaluate_node(nid, subset, nodes, memo, TRUE, FALSE):
    """
    Standalone evaluator with its own memoization dict passed by reference.
    """
    if nid in memo:
        return memo[nid]

    if nid == TRUE: return True
    if nid == FALSE: return False

    op, l, r = nodes[nid]

    if l is None:  # Atomic Proposition
        res = nid in subset
    elif op in ('~', '!'):
        res = not evaluate_node(l, subset, nodes, memo, TRUE, FALSE)
    elif op == '&':
        res = evaluate_node(l, subset, nodes, memo, TRUE, FALSE) and evaluate_node(r, subset, nodes, memo, TRUE, FALSE)
    elif op == '|':
        res = evaluate_node(l, subset, nodes, memo, TRUE, FALSE) or evaluate_node(r, subset, nodes, memo, TRUE, FALSE)
    elif op == 'U':
        if nid not in subset and evaluate_node(r, subset, nodes, memo, TRUE, FALSE):
            # Until is evaluated not true in the subset, but the right part is true
            res = False
        elif nid in subset and not (evaluate_node(l, subset, nodes, memo, TRUE, FALSE) or evaluate_node(r, subset, nodes, memo, TRUE,FALSE)):
            # Until is evaluated true in the subset, but bot l and r are false
            res = False
        else:
            # U is evaluated true in the subset, and either l or r is true
            res = nid in subset
    elif op == 'R':
        if nid not in subset and (evaluate_node(l, subset, nodes, memo, TRUE, FALSE) and evaluate_node(r, subset, nodes, memo, TRUE, FALSE)):
            # R is evaluated not true, but l and r are evaluated true
            res = False
        elif nid in subset and not evaluate_node(r, subset, nodes, memo, TRUE, FALSE):
            # R is evaluated true, but r is not true yet.
            res = False
        else:
            # R is evaluated true, and either both l and r are true, or r is true
            res = nid in subset
    elif op == 'X':
        res = nid in subset
    else:
        res = False

    memo[nid] = res
    return res


def is_consistent(dag, subset, closure):
    """
    Checks if a subset is consistent with the closure
    It determines if the subset is allowed based on the true APs of the subset and what formula's from the closure these true APs enforce.
    """
    nodes = dag._nodes
    TRUE = dag._index.get(('true', None, None))
    FALSE = dag._index.get(('false', None, None))

    memo = {}

    # 1. Constant constraints
    if TRUE is not None and TRUE in closure and TRUE not in subset:
        return False
    if FALSE is not None and FALSE in subset:
        return False

    # 2. Structural/Semantic constraints
    for nid in closure:
        op, l, r = nodes[nid]

        if not evaluate_node(nid, subset, nodes, memo, TRUE, FALSE) and nid in subset:
            # the node evaluates to false, but is in subset
            return False

        if (op == '&' and
                evaluate_node(l, subset, nodes, memo, TRUE, FALSE) and evaluate_node(r, subset, nodes, memo, TRUE,FALSE) and
                nid not in subset):
            # both a and b are true, but (a & b) is not in the subset
            return False
        if (op == '|' and
                (evaluate_node(l, subset, nodes, memo, TRUE, FALSE) or evaluate_node(r, subset, nodes, memo, TRUE, FALSE)) and
                nid not in subset):
            # either a or b or both are true, but (a | b) is not in the subset
            return False
        if op == 'U' and evaluate_node(r, subset, nodes, memo, TRUE, FALSE) and nid not in subset:
            # r is true, but (l U r) is false in the subset
            return False
        if op == 'R' and evaluate_node(l, subset, nodes, memo, TRUE, FALSE) and evaluate_node(r, subset, nodes, memo, TRUE, FALSE) and nid not in subset:
            # both r and l are true, but (l R r) is false in the subset.
            return False
    return True


def resolve_polarity(nodes, nid):
    """
    Follow a chain of ~/! nodes down to the underlying closure member.

    Returns (base_nid, positive) where base_nid is the first non-negation node
    reached and positive says whether the original node holds exactly when
    base_nid holds (True) or exactly when it does not (False).
    """
    positive = True
    while nodes[nid][0] in ('~', '!'):
        nid = nodes[nid][1]
        positive = not positive
    return nid, positive


def get_gnba_successors_lazy(dag, current_state, closure):
    """
    Lazy GNBA successor generator.
    Derives next-state properties directly from the current state rules.
    """
    nodes = dag._nodes
    closure_list = sorted(closure)
    TRUE = dag._index.get(('true', None, None))
    FALSE = dag._index.get(('false', None, None))
    eval_memo = {}

    # 1. Deduce absolute requirements for the candidate successor state
    must_have = set()
    must_not_have = set()

    for nid in closure:
        op, l, r = nodes[nid]

        if op == 'X':
            # Next-step rule: X(l) in current_state <=> l MUST hold in next state.
            # `l` may be a bare negation (e.g. `X ~p` from PNF), which is never a
            # closure member, so I use resolve_polarity()
            base, positive = resolve_polarity(nodes, l)
            l_must_hold = (nid in current_state)
            if l_must_hold == positive:
                must_have.add(base)
            else:
                must_not_have.add(base)

        elif op == 'U':
            u_in_now = nid in current_state
            # l/r may be bare negations (or other composites) that are never
            # closure members themselves, so their truth must be *evaluated*,
            # not looked up via raw membership in current_state.
            r_in_now = evaluate_node(r, current_state, nodes, eval_memo, TRUE, FALSE)
            l_in_now = evaluate_node(l, current_state, nodes, eval_memo, TRUE, FALSE)
            # Step rule for Until: if u is true now but r isn't satisfied yet,
            # then u must persist into the next state.
            if u_in_now and not r_in_now:
                must_have.add(nid)
            # If U is false and l is true now, the next state may not have it, since:
            # l U r == r | (l & X(l U r) )
            # if the next step would have it, than the U would have been true.
            elif not u_in_now and l_in_now:
                must_not_have.add(nid)

        elif op == 'R':
            r_in_now = nid in current_state
            l_satisfied = evaluate_node(l, current_state, nodes, eval_memo, TRUE, FALSE)
            r_satisfied = evaluate_node(r, current_state, nodes, eval_memo, TRUE, FALSE)

            # Rule 1: If R is active, but the unlocking condition (l) hasn't
            # triggered yet, the R must roll over to the next state.
            if r_in_now and not l_satisfied:
                must_have.add(nid)

            # Rule 2: If R is inactive, but its r is true,
            # it means the next state is forced to break the release rule.
            elif not r_in_now and r_satisfied:
                must_not_have.add(nid)

    # Quick check: If an element is simultaneously forced to be true and false, exit early
    if not must_have.isdisjoint(must_not_have):
        return

    # 2. Backtrack and branch only over the remaining unconstrained nodes in the closure
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


def generate_initial_states(dag, closure, root):
    """
    generates initial states by forcing `root` into every candidate.
    Halves (at minimum) the backtracking tree and avoids materialising
    unreachable non-initial states entirely.
    """
    closure_list = sorted(closure)
    TRUE  = dag._index.get(('true',  None, None))
    FALSE = dag._index.get(('false', None, None))

    def backtrack(index, current_set):
        if index == len(closure_list):
            candidate = frozenset(current_set)
            if is_consistent(dag, candidate, closure):
                yield candidate
            return

        nid = closure_list[index]

        if nid == TRUE or nid == root:      # always included (root wins over FALSE:
            current_set.add(nid)            # a `false` PNF root is forced in, then
            yield from backtrack(index + 1, current_set)  # rejected by is_consistent,
            current_set.remove(nid)         # so a trivially-true property yields no
        elif nid == FALSE:                  # initial states rather than over-accepting)
            yield from backtrack(index + 1, current_set)
        else:                               # free to branch
            yield from backtrack(index + 1, current_set)   # exclude
            current_set.add(nid)
            yield from backtrack(index + 1, current_set)   # include
            current_set.remove(nid)

    yield from backtrack(0, set())


def get_label(dag, state):
    """returns the true atomic propositions from the dag representation"""
    nodes = dag._nodes
    true_aps = set()

    for nid in state:
        op, l, r = nodes[nid]
        if l is None and op not in ('true', 'false'):
            true_aps.add(op)

    return frozenset(true_aps)


def compute_acceptance(dag, states, closure):
    """computes the acceptance set(s)"""
    nodes = dag._nodes
    acceptance = []
    TRUE = dag._index.get(('true', None, None))
    FALSE = dag._index.get(('false', None, None))

    for nid in sorted(closure):
        op, l, r = nodes[nid]
        if op == 'U':
            # r may be a bare negation (never a closure member itself), so its
            # truth in s must be evaluated rather than checked via membership.
            acc = frozenset(
                s for s in states
                if nid not in s or evaluate_node(r, s, nodes, {}, TRUE, FALSE)
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
    """
    Builds the GNBA by only exploring states that are actually reachable
    from the initial states, utilizing the lazy successor generator.
    """
    closure = compute_closure(dag, root)

    # 1. Find the initial states out of all locally consistent options.
    initial_states = list(generate_initial_states(dag, closure, root))
    if not initial_states:
        raise ValueError("No consistent initial states — formula may be unsatisfiable.")

    if not initial_states:
        raise ValueError("No consistent initial states — formula may be unsatisfiable.")

    # 2. Graph Traversal (BFS) to discover reachable states and transitions
    discovered_states = []
    state_to_idx = {}

    # Register initial states
    initial_indices = []
    for s in initial_states:
        if s not in state_to_idx:
            state_to_idx[s] = len(discovered_states)
            discovered_states.append(s)
        initial_indices.append(state_to_idx[s])

    transitions = {}
    queue = list(initial_states)
    processed = set()

    while queue:
        current_state = queue.pop(0)
        if current_state in processed:
            continue
        processed.add(current_state)

        src_idx = state_to_idx[current_state]
        transitions[src_idx] = []

        # Use your lazy generator to find ONLY valid neighbors!
        for lbl, next_state in get_gnba_successors_lazy(dag, current_state, closure):
            if next_state not in state_to_idx:
                state_to_idx[next_state] = len(discovered_states)
                discovered_states.append(next_state)
                queue.append(next_state)

            dst_idx = state_to_idx[next_state]
            transitions[src_idx].append((lbl, dst_idx))

    # 3. Clean up AP names
    d = dag._nodes
    ap_names = sorted({
        op
        for nid in closure
        for (op, l, r) in [d[nid]]
        if l is None and op not in ('true', 'false')
    })

    # 4. Compute acceptance sets over discovered states only
    acceptance = compute_acceptance(dag, discovered_states, closure)

    return GNBA(discovered_states, initial_indices, transitions, acceptance, ap_names)


# =========================================================
# HOA OUTPUT & DOT UTILITIES
# =========================================================

def to_hoa(gnba: GNBA, formula_str=""):
    """
    Serialises the GNBA to the HOA v1 format (https://adl.github.io/hoaf/).
    Acceptance is state-based generalized-Buchi: Inf(0)&Inf(1)&...&Inf(k-1),
    one Inf(i) per acceptance set in gnba.acceptance.
    """
    ap_names = gnba.ap_names
    ap_index = {name: i for i, name in enumerate(ap_names)}
    n_acc = len(gnba.acceptance)

    def guard_for(lbl):
        if not ap_names:
            return "t"
        return "&".join(
            str(ap_index[name]) if name in lbl else f"!{ap_index[name]}"
            for name in ap_names
        )

    def acc_sig(state_content):
        sets = [i for i, acc in enumerate(gnba.acceptance) if state_content in acc]
        return "{" + " ".join(str(i) for i in sets) + "}" if sets else ""

    lines = ["HOA: v1"]
    if formula_str:
        lines.append(f'name: "GNBA for {formula_str}"')
    lines.append(f"States: {len(gnba.states)}")
    for i in gnba.initial:
        lines.append(f"Start: {i}")
    lines.append(f"AP: {len(ap_names)}" + "".join(f' "{n}"' for n in ap_names))

    if n_acc == 0:
        lines.append("acc-name: all")
        lines.append("Acceptance: 0 t")
    elif n_acc == 1:
        lines.append("acc-name: Buchi")
        lines.append("Acceptance: 1 Inf(0)")
    else:
        lines.append(f"acc-name: generalized-Buchi {n_acc}")
        lines.append(f"Acceptance: {n_acc} " + "&".join(f"Inf({i})" for i in range(n_acc)))

    lines.append("properties: trans-labels explicit-labels state-acc")
    lines.append("--BODY--")

    for i in range(len(gnba.states)):
        sig = acc_sig(gnba.states[i])
        lines.append(f"State: {i}" + (f" {sig}" if sig else ""))
        for lbl, dst in gnba.transitions.get(i, []):
            lines.append(f"[{guard_for(lbl)}] {dst}")

    lines.append("--END--")
    return "\n".join(lines)

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
