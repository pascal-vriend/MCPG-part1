import subprocess

from part1.models.ltl_model import LTLDAG, to_pnf
from part1.models.GNBA import build_gnba, to_dot, compute_closure, generate_consistent_states
from part1.models.NBA import degeneralize_to_nba, nba_to_dot

from part1.parsers.ltl import LTLParser

from part1.tools.nested_dfs import nested_dfs
from part1.tools.prune_automaton import prune_automaton_unreachable

PRUNE_ENABLED = False
SHOW_STATES = True


def print_state_subformulas(states_iterable, gnba_reference, dag, label_prefix=""):
    print(f"\n--- State Composition Details ({label_prefix}) ---")
    sorted_states = sorted(list(states_iterable), key=lambda x: str(x))
    gnba_states_list = list(gnba_reference.states)

    for idx, state in enumerate(sorted_states):
        layer_info = ""

        # Case 1: NBA Tuple State (gnba_state_frozenset, layer)
        if isinstance(state, tuple) and len(state) == 2:
            inner_state, layer = state
            layer_info = f" [Layer {layer}]"

            if isinstance(inner_state, (set, frozenset)):
                try:
                    g_idx = gnba_states_list.index(inner_state)
                    state_label = f"NBA State N{idx} (S{g_idx})"
                except ValueError:
                    state_label = f"NBA State N{idx}"
                formulas_in_state = inner_state
            else:
                state_label = f"NBA State {state}"
                formulas_in_state = inner_state

        # Case 2: Direct GNBA state representation
        else:
            state_label = f"GNBA State S{idx}"
            formulas_in_state = state

        # Extract contents safely
        if isinstance(formulas_in_state, (set, frozenset)):
            raw_set = formulas_in_state
        else:
            raw_set = None

        if raw_set is not None:
            if not raw_set:
                print(f"  {state_label}{layer_info}: {{ Ø }}")
            else:
                sub_strs = [dag.to_infix(nid) if isinstance(nid, int) else str(nid) for nid in sorted(list(raw_set))]
                print(f"  {state_label}{layer_info}: {{{', '.join(sub_strs)}}}")
        else:
            print(f"  {state_label}{layer_info}: {state}")

    print("-" * 50)


def run_pipeline(formula_str, build_gnba_flag=True, build_nba_flag=True, run_check_flag=True):
    global PRUNE_ENABLED, SHOW_STATES

    dag = LTLDAG()
    parser = LTLParser(dag)

    try:
        nid = parser(formula_str)
    except Exception as e:
        print(f"❌ Parse error: {e}")
        return

    pnf_root = to_pnf(dag, nid)
    infix_str = dag.to_infix(pnf_root)
    closure = compute_closure(dag, pnf_root)
    readable_closure = [dag.to_infix(nid) for nid in closure]
    readable_closure.sort()

    print("\n" + "=" * 50)
    print(f"Parsing Formula: {dag.to_infix(nid)}")
    print(f"PNF Form       : {infix_str}")
    print(f"Closure        : {readable_closure}")
    print("=" * 50)

    until_formulas = [nid for nid in closure if dag._nodes[nid][0] == 'U']
    k_layers = len(until_formulas) if until_formulas else 1

    # Build the exact semantic map needed by the lazy successor routines
    all_consistent_frozensets = list(generate_consistent_states(dag, closure))

    if k_layers == 1:
        gnba_acc_sets = {1: frozenset(all_consistent_frozensets)}
    else:
        gnba_acc_sets = {}
        for layer_idx, u_nid in enumerate(until_formulas, start=1):
            r_nid = dag._nodes[u_nid][2]
            gnba_acc_sets[layer_idx] = frozenset(s for s in all_consistent_frozensets
                                                 if u_nid not in s or r_nid in s)

    # -------------------------------------------------------------
    # EXECUTE CHECK (Pure On-The-Fly Execution)
    # -------------------------------------------------------------
    if run_check_flag:
        print("\n🔍 Running Pure On-the-Fly Nested DFS Emptiness Check...")
        is_sat, witness_path = nested_dfs(dag, pnf_root, closure, gnba_acc_sets, k_layers)

        print("=" * 50)
        if is_sat:
            print("🎉 RESULT: Formula is SATISFIABLE!")

            # Find the loop entry point by tracking duplicates
            seen_states = {}
            loop_entry_idx = -1

            # Populate our seen dictionary to catch the point where the lasso closes
            for idx, state in enumerate(witness_path):
                if state in seen_states:
                    loop_entry_idx = seen_states[state]
                    break
                seen_states[state] = idx

            print("Witness Execution Path found:")
            for idx, (f_set, layer) in enumerate(witness_path):
                formulas_str = ", ".join(dag.to_infix(nid) for nid in sorted(list(f_set)))

                # Check for visual annotations
                prefix = "  --> " if idx > 0 else "      "
                annotation = ""
                if idx == loop_entry_idx:
                    annotation = "  📌 [LOOP ENTRY POINT]"
                elif idx == len(witness_path) - 1 and loop_entry_idx != -1:
                    annotation = f"  ↩️ [LOOP BACK TO STEP {loop_entry_idx + 1}]"

                print(f"{prefix}(Step {idx + 1} | Layer {layer}: {{{formulas_str}}}){annotation}")
        else:
            print("❌ RESULT: Formula is UNSATISFIABLE! (No accepting lasso found)")
        print("=" * 50)

    # -------------------------------------------------------------
    # CASE B: EXPLICIT AUTOMATA MODE (Builds, prunes, and saves images)
    # -------------------------------------------------------------
    gnba = None
    if build_gnba_flag or build_nba_flag:
        try:
            gnba = build_gnba(dag, pnf_root)
        except ValueError as e:
            print(f"❌ GNBA Generation Error: {e}")
            return

        if PRUNE_ENABLED:
            print("[System Info] Pruning unreachable GNBA states active.")
            prune_automaton_unreachable(gnba)

        print(f"✅ GNBA generated successfully. States: {len(gnba.states)}")
        if SHOW_STATES:
            print_state_subformulas(gnba.states, gnba, dag, label_prefix="GNBA")

        # Export GNBA DOT
        with open("../outputs/gnba.dot", "w", encoding="utf-8") as f:
            f.write(to_dot(gnba, dag=dag, formula_str=infix_str))
        _render_png("gnba")

    if build_nba_flag and gnba:
        print("\n🔄 Degeneralizing GNBA into NBA layers...")
        nba = degeneralize_to_nba(gnba)

        if PRUNE_ENABLED:
            print("[System Info] Pruning unreachable NBA states active.")
            prune_automaton_unreachable(nba)

        print(f"✅ NBA generated successfully. States: {len(nba.states)}")
        if SHOW_STATES:
            print_state_subformulas(nba.states, gnba, dag, label_prefix="NBA")

        # Export NBA DOT
        nba_dot = nba_to_dot(nba, dag, gnba, formula_str=infix_str, prune_enabled=PRUNE_ENABLED)
        with open("../outputs/nba.dot", "w", encoding="utf-8") as f:
            f.write(nba_dot)
        _render_png("nba")

def _render_png(name):
    try:
        subprocess.run(["dot", "-Tpng", f"../outputs/{name}.dot", "-o", f"../outputs/{name}.png"],
                       capture_output=True, text=True)
        print(f"🖼️  Rendered graphic output saved to '../outputs/{name}.png'")
    except FileNotFoundError:
        pass


def main():
    global PRUNE_ENABLED, SHOW_STATES
    print(f"https://dreampuf.github.io/GraphvizOnline/")
    while True:
        user_input = input("\nEnter LTL Formula or Config Command: ").strip()
        if not user_input:
            continue
        if user_input.lower() == "exit":
            print("Goodbye!")
            break

        # Check for system updates first
        if user_input.startswith("--") or "show-states" in user_input.lower() or "prune" in user_input.lower():
            cleaned_cmd = user_input.lower().replace(" ", "")
            if cleaned_cmd in ("--prune", "prune=true"):
                PRUNE_ENABLED = True
                print(">> System configuration updated: Pruning ENABLED.")
            elif cleaned_cmd in ("--no-prune", "prune=false"):
                PRUNE_ENABLED = False
                print(">> System configuration updated: Pruning DISABLED.")
            elif cleaned_cmd in ("--show-states", "show-states=true"):
                SHOW_STATES = True
                print(">> System configuration updated: Show State Composition ENABLED.")
            elif cleaned_cmd in ("--hide-states", "show-states=false"):
                SHOW_STATES = False
                print(">> System configuration updated: Show State Composition DISABLED.")
            continue

        # Parse formula and arguments (e.g., GFa --gnba --check)
        parts = user_input.split()

        # The first part (or anything not starting with --) forms the LTL formula core
        formula_parts = [p for p in parts if not p.startswith("--")]
        flags = [p.lower() for p in parts if p.startswith("--")]

        formula_str = " ".join(formula_parts)

        # Set execution defaults based on flags
        if flags:
            build_gnba_flag = "--gnba" in flags
            build_nba_flag = "--nba" in flags
            run_check_flag = "--check" in flags
        else:
            # If the user types a raw formula with NO flags, run all stages by default
            build_gnba_flag = True
            build_nba_flag = True
            run_check_flag = True

        run_pipeline(formula_str, build_gnba_flag, build_nba_flag, run_check_flag)


if __name__ == "__main__":
    main()
