from part1.models.GNBA import generate_initial_states
from part1.models.NBA import get_nba_successors_lazy


def nested_dfs(dag, pnf_root, closure, gnba_acc_sets, k,
               get_successors_fn=get_nba_successors_lazy,
               initial_states_override=None):
    """
    Pure On-The-Fly Nested DFS with live state exploration tracking.
    """
    blue_visited = set()
    red_visited = set()
    blue_stack = []
    red_stack = []

    states_explored = 0

    if initial_states_override is not None:
        structural_initials = initial_states_override
    else:
        structural_initials = (
            (s, 1)
            for s in generate_initial_states(dag, closure, pnf_root)  # ← pin pnf_root
        )

    blue_stack_set = set()

    def is_nba_state_accepting(nba_state):
        actual_nba = nba_state[1] if isinstance(nba_state[0], tuple) else nba_state
        g_src, copy_num = actual_nba
        if copy_num != 1:
            return False
        return gnba_acc_sets[1](g_src)

    def dfs_red(v):
        nonlocal states_explored
        red_visited.add(v)
        red_stack.append(v)

        for lbl, w in get_successors_fn(dag, v, closure, gnba_acc_sets, k):
            if w in blue_stack_set:
                red_stack.append(w)
                return True

            if w not in red_visited:
                states_explored += 1
                if states_explored % 50000 == 0:
                    print(f"       [Progress] Discovered {states_explored} unique states...")
                if dfs_red(w):
                    return True

        red_stack.pop()
        return False

    def dfs_blue(v):
        nonlocal states_explored

        blue_visited.add(v)
        blue_stack.append(v)
        blue_stack_set.add(v)

        for lbl, w in get_successors_fn(dag, v, closure, gnba_acc_sets, k):
            if w not in blue_visited:
                states_explored += 1
                if states_explored % 50000 == 0:
                    print(f"       [Progress] Discovered {states_explored} unique states...")
                if dfs_blue(w):
                    return True

        if is_nba_state_accepting(v):
            if v not in red_visited:
                if dfs_red(v):
                    return True

        blue_stack_set.remove(v)
        blue_stack.pop()
        return False

    # Main Search Loop
    print(" Running nested DFS on the automaton...")
    for init_state in structural_initials:
        if init_state not in blue_visited:
            if dfs_blue(init_state):
                print(f"Verification complete! Explored a total of {states_explored} states.")

                #  Slice red_stack[1:] to prevent duplicating the accepting state.
                # `blue_stack` ends with `v` and `red_stack` starts with `v`.
                full_witness = list(blue_stack) + list(red_stack)[1:]

                return True, full_witness

    print(f" Verification complete! No violating cycle found. Checked {states_explored} states.")
    return False, []