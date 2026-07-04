def prune_automaton_unreachable(automaton):
    """
    Unified structural optimization tool.
    Prunes unreachable states from any explicit automaton (GNBA or NBA)
    and remaps sequential state index IDs in-place.
    """
    # 1. Discover reachable state indices via Frontier Traversal
    reachable = set(automaton.initial)
    frontier = list(automaton.initial)

    while frontier:
        curr = frontier.pop()
        # Fallback to an empty list if a state has no declared transitions
        transitions = (automaton.transitions.get(curr, [])
                       if isinstance(automaton.transitions, dict)
                       else automaton.transitions[curr])

        for _, nxt in transitions:
            if nxt not in reachable:
                reachable.add(nxt)
                frontier.append(nxt)

    # 2. Build index tracking conversion maps
    sorted_reachable = sorted(reachable)
    old_to_new = {old: new for new, old in enumerate(sorted_reachable)}

    # 3. Remap states, initials, and explicit transition tables
    automaton.states = [automaton.states[i] for i in sorted_reachable]
    automaton.initial = [old_to_new[i] for i in automaton.initial]
    automaton.transitions = {
        old_to_new[i]: [(lbl, old_to_new[j]) for lbl, j in (
            automaton.transitions.get(i, []) if isinstance(automaton.transitions, dict) else automaton.transitions[i])]
        for i in sorted_reachable
    }

    # 4. Polymorphic Acceptance Remapping (Handles the collection discrepancy)
    if isinstance(automaton.acceptance, (set, frozenset)):
        # NBA Strategy: Single Set conversion
        automaton.acceptance = frozenset(
            old_to_new[i] for i in automaton.acceptance if i in reachable
        )
    else:
        # GNBA Strategy: List of Sets conversion
        automaton.acceptance = [
            frozenset(old_to_new[i] for i in acc if i in reachable)
            for acc in automaton.acceptance
        ]