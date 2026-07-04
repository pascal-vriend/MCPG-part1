from part1.models.GNBA import GNBA, get_gnba_successors_lazy


class NBA:
    def __init__(self, states, initial, transitions, acceptance, ap_names):
        # states: list of tuples (gnba_state_index, copy_index)
        self.states = states
        self.initial = initial  # list of NBA state indices
        self.transitions = transitions  # dict: nba_idx -> list of (lbl, nba_dst_idx)
        self.acceptance = acceptance  # frozenset of NBA state indices (Single set!)
        self.ap_names = ap_names


def degeneralize_to_nba(gnba: GNBA):
    k = len(gnba.acceptance)
    ap_names = gnba.ap_names

    # Edge case: If there are no acceptance sets (no U operators in formula),
    # everything is unconditionally accepting. We treat it as 1 trivial copy.
    if k == 0:
        gnba_acc_sets = {1: frozenset(gnba.states)}  # Changed to store frozensets directly
        k = 1
    else:
        # Map your GNBA acceptance sets to 1-based indexing to match slides:
        # F_1 is gnba.acceptance[0], F_2 is gnba.acceptance[1], etc.
        gnba_acc_sets = {i + 1: gnba.acceptance[i] for i in range(k)}

    nba_states = []
    state_to_idx = {}

    # 1. Create k copies of each state (using 1-based index for copies)
    for copy_num in range(1, k + 1):
        for g_idx in range(len(gnba.states)):
            actual_frozenset = gnba.states[g_idx]  # Get the subformula set
            nba_state = (actual_frozenset, copy_num)  # Track structurally
            nba_states.append(nba_state)
            state_to_idx[nba_state] = len(nba_states) - 1

    # 2. Initial states: Translate the integer index g_init to its actual frozenset
    nba_initial = [state_to_idx[(gnba.states[g_init], 1)] for g_init in gnba.initial]

    # 3. Build Transitions based on your slide rules
    nba_transitions = {idx: [] for idx in range(len(nba_states))}

    for (g_src, current_copy), src_idx in state_to_idx.items():
        # Check the slide condition: does the GNBA state belong to F_i?
        if g_src in gnba_acc_sets[current_copy]:
            # Move to copy i + 1 (cyclically)
            next_copy = (current_copy % k) + 1
        else:
            # Stay in copy i
            next_copy = current_copy

        # Replicate the edges to the target copy
        # Since gnba.transitions maps an integer src to a list of (lbl, integer_dst),
        # we look up the integer index of g_src first to pull its transitions.
        g_src_idx = gnba.states.index(g_src)

        for lbl, g_dst_idx in gnba.transitions.get(g_src_idx, []):
            actual_g_dst = gnba.states[g_dst_idx]  # Convert int index to frozenset
            dst_idx = state_to_idx[(actual_g_dst, next_copy)]
            nba_transitions[src_idx].append((lbl, dst_idx))

    # 4. Accepting states: Translate the tracking structure index to match
    nba_acceptance = frozenset(
        state_to_idx[(gnba.states[g_idx], 1)]
        for g_idx in range(len(gnba.states))
        if gnba.states[g_idx] in gnba_acc_sets[1]
    )

    return NBA(nba_states, nba_initial, nba_transitions, nba_acceptance, ap_names)


def label_to_hoa(true_aps, ap_names):
    if not ap_names:
        return "t"
    return " & ".join(ap if ap in true_aps else f"!{ap}" for ap in ap_names)


def get_nba_successors_lazy(dag, current_nba_state, closure, gnba_acc_sets, k):
    """
    On-The-Fly Degeneralization Generator for NBA.
    current_nba_state is a tuple: (gnba_state_frozenset, current_copy)
    """
    # ─── ADD THIS DEFENSIVE CHECK HERE ──────────────────────────────────────
    if len(current_nba_state) == 2 and isinstance(current_nba_state[1], tuple):
        # Product Space Mode: State is (marking, (gnba_frozenset, copy_int))
        _, (g_src, current_copy) = current_nba_state
    else:
        # Pure LTL Pipeline Mode: State is just (gnba_frozenset, copy_int)
        g_src, current_copy = current_nba_state
    # ────────────────────────────────────────────────────────────────────────

    # 1. Calculate the target copy tracking variable based on slide rules
    if g_src in gnba_acc_sets[current_copy]:
        next_copy = (current_copy % k) + 1
    else:
        next_copy = current_copy

    # 2. Lazily pull GNBA successors and map them into the calculated next copy
    for lbl, g_dst in get_gnba_successors_lazy(dag, g_src, closure):
        next_nba_state = (g_dst, next_copy)
        yield lbl, next_nba_state


def nba_to_dot(nba: NBA, dag, gnba: GNBA, formula_str="", prune_enabled=True):
    lines = []
    lines.append("digraph NBA {")
    lines.append('  rankdir=LR;')
    lines.append('  node [shape=circle, fontname="Helvetica"];')
    if formula_str:
        suffix = " (Pruned)" if prune_enabled else " (Unpruned)"
        lines.append(f'  label="NBA: {formula_str}{suffix}";')
        lines.append('  labelloc=t;')
    lines.append("")

    for i in nba.initial:
        lines.append(f'  __init_{i} [shape=point, style=invis, width=0];')
    lines.append("")

    for i in range(len(nba.states)):
        state_frozenset, copy_num = nba.states[i]
        is_acc = i in nba.acceptance
        shape_attr = 'shape=doublecircle' if is_acc else 'shape=circle'

        # Find what index this frozenset had in the original GNBA object
        try:
            g_idx = gnba.states.index(state_frozenset)
        except ValueError:
            g_idx = "?"

        # State label displays its sequential index and its original copy location
        label = f'N{i}\\n(S{g_idx}, C{copy_num})'

        extra = ', style=filled, fillcolor=lightblue' if i in nba.initial else ''
        lines.append(f'  {i} [label="{label}", {shape_attr}{extra}];')

    lines.append("")
    for i in nba.initial:
        lines.append(f'  __init_{i} -> {i};')
    lines.append("")

    edge_labels = {}
    for i, trans in nba.transitions.items():
        for lbl, j in trans:
            lbl_str = label_to_hoa(lbl, nba.ap_names)
            edge_labels.setdefault((i, j), []).append(lbl_str)

    for (i, j), labels in sorted(edge_labels.items()):
        unique = list(dict.fromkeys(labels))
        combined = "\\n".join(unique)
        lines.append(f'  {i} -> {j} [label="{combined}"];')

    # Legend table for clear node inspections
    lines.append("")
    lines.append("  subgraph cluster_legend {")
    lines.append('    label="NBA Legend"; fontname="Helvetica"; style=dashed;')
    lines.append('    node [shape=none, margin=0];')
    lines.append('    legend [label=<')
    lines.append('      <TABLE BORDER="0" CELLBORDER="1" CELLSPACING="0" CELLPADDING="4">')
    lines.append(
        '        <TR><TD><B>NBA State</B></TD><TD><B>GNBA State</B></TD><TD><B>Copy</B></TD><TD><B>GNBA Contents</B></TD></TR>')
    for i, (state_frozenset, copy_num) in enumerate(nba.states):
        try:
            g_idx = gnba.states.index(state_frozenset)
            contents = ", ".join(dag.to_infix(n) for n in sorted(state_frozenset))
        except ValueError:
            g_idx = "?"
            contents = "Unknown"

        lines.append(
            f'        <TR><TD ALIGN="LEFT">N{i}</TD>'
            f'<TD ALIGN="LEFT">S{g_idx}</TD>'
            f'<TD ALIGN="LEFT">Copy {copy_num}</TD>'
            f'<TD ALIGN="LEFT">{{ {contents} }}</TD></TR>'
        )
    lines.append('      </TABLE>>];')
    lines.append("  }")
    lines.append("}")
    return "\n".join(lines)
