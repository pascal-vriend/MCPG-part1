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
    """used only if the GNBa is already generated and we want to make it into a NBA"""
    k = len(gnba.acceptance)
    ap_names = gnba.ap_names

    # Edge case: If there are no acceptance sets (no U operators in formula),
    # everything is unconditionally accepting. We treat it as 1 trivial copy.
    if k == 0:
        gnba_acc_sets = {1: frozenset(gnba.states)}
        k = 1
    else:
        # index starts at 1 so F_1 is gnba.acceptance[0], F_2 is gnba.acceptance[1], etc.
        gnba_acc_sets = {i + 1: gnba.acceptance[i] for i in range(k)}

    nba_states = []
    state_to_idx = {}

    # 1. Create k copies of each state
    for copy_num in range(1, k + 1):
        for g_idx in range(len(gnba.states)):
            actual_frozenset = gnba.states[g_idx]  # Get the subformula set
            nba_state = (actual_frozenset, copy_num)  # Track structurally
            nba_states.append(nba_state)
            state_to_idx[nba_state] = len(nba_states) - 1

    # 2. Initial states: Translate the integer index g_init to its actual frozenset
    nba_initial = [state_to_idx[(gnba.states[g_init], 1)] for g_init in gnba.initial]

    # 3. Build Transitions
    nba_transitions = {idx: [] for idx in range(len(nba_states))}

    for (g_src, current_copy), src_idx in state_to_idx.items():
        # Check: does the GNBA state belong to F_i?
        if g_src in gnba_acc_sets[current_copy]:
            # Move to copy i + 1 (cyclically)
            next_copy = (current_copy % k) + 1
        else:
            # Stay in copy i
            next_copy = current_copy

        # Replicate the edges to the target copy
        # Since gnba.transitions maps an integer src to a list of (lbl, integer_dst),
        # I look up the integer index of g_src first to pull its transitions.
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


def nba_to_hoa(nba: NBA, formula_str=""):
    """
    Serialises the degeneralized NBA to the HOA v1 format
    (https://adl.github.io/hoaf/). Acceptance is state-based Buchi: Inf(0).
    """
    ap_names = nba.ap_names
    ap_index = {name: i for i, name in enumerate(ap_names)}

    def guard_for(lbl):
        if not ap_names:
            return "t"
        return "&".join(
            str(ap_index[name]) if name in lbl else f"!{ap_index[name]}"
            for name in ap_names
        )

    lines = ["HOA: v1"]
    if formula_str:
        lines.append(f'name: "NBA for {formula_str}"')
    lines.append(f"States: {len(nba.states)}")
    for i in nba.initial:
        lines.append(f"Start: {i}")
    lines.append(f"AP: {len(ap_names)}" + "".join(f' "{n}"' for n in ap_names))
    lines.append("acc-name: Buchi")
    lines.append("Acceptance: 1 Inf(0)")
    lines.append("properties: trans-labels explicit-labels state-acc")
    lines.append("--BODY--")

    for i in range(len(nba.states)):
        sig = " {0}" if i in nba.acceptance else ""
        lines.append(f"State: {i}{sig}")
        for lbl, dst in nba.transitions.get(i, []):
            lines.append(f"[{guard_for(lbl)}] {dst}")

    lines.append("--END--")
    return "\n".join(lines)


def get_nba_successors_lazy(dag, current_nba_state, closure, gnba_acc_sets, k):
    """
    On-The-Fly Degeneralization Generator for NBA. It uses the lazy generator of GNBA so no explicit GNBA is generated.
    current_nba_state is a tuple: (gnba_state_frozenset, current_copy)
    """
    # check if it is a product automaton or a normal nba.
    if len(current_nba_state) == 2 and isinstance(current_nba_state[1], tuple):
        # Product Space Mode: State is (marking, (gnba_frozenset, copy_int))
        _, (g_src, current_copy) = current_nba_state
    else:
        # Pure LTL Pipeline Mode: State is just (gnba_frozenset, copy_int)
        g_src, current_copy = current_nba_state
    # ────────────────────────────────────────────────────────────────────────

    # 1. Calculate the target copy tracking variable
    if gnba_acc_sets[current_copy](g_src):
        next_copy = (current_copy % k) + 1
    else:
        next_copy = current_copy

    # 2. Lazily pull GNBA successors and map them into the calculated next copy
    for lbl, g_dst in get_gnba_successors_lazy(dag, g_src, closure):
        next_nba_state = (g_dst, next_copy)
        yield lbl, next_nba_state


def nba_to_dot(nba: NBA, dag, gnba: GNBA, formula_str=""):
    def _html_escape(s):
        return s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")

    lines = []
    lines.append("digraph NBA {")
    lines.append('  rankdir=LR;')
    lines.append('  node [shape=circle, fontname="Helvetica"];')
    if formula_str:
        lines.append(f'  label="NBA: {formula_str}";')
        lines.append('  labelloc=t;')
    lines.append("")

    for i in nba.initial:
        lines.append(f'  __init_{i} [shape=point, style=invis, width=0];')
    lines.append("")

    for i in range(len(nba.states)):
        state_frozenset, copy_num = nba.states[i]
        is_acc = i in nba.acceptance
        shape_attr = 'shape=doublecircle' if is_acc else 'shape=circle'

        try:
            g_idx = gnba.states.index(state_frozenset)
        except ValueError:
            g_idx = "?"

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

        # Apply HTML escaping to the generated text strings
        n_str = _html_escape(f"N{i}")
        s_str = _html_escape(f"S{g_idx}")
        c_str = _html_escape(f"Copy {copy_num}")
        cont_str = _html_escape("{ " + contents + " }")

        lines.append(
            f'        <TR><TD ALIGN="LEFT">{n_str}</TD>'
            f'<TD ALIGN="LEFT">{s_str}</TD>'
            f'<TD ALIGN="LEFT">{c_str}</TD>'
            f'<TD ALIGN="LEFT">{cont_str}</TD></TR>'
        )

    lines.append('      </TABLE>>];')
    lines.append("  }")
    lines.append("}")
    return "\n".join(lines)
