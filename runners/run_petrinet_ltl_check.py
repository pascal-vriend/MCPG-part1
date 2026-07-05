import gc
import threading
import os
import sys
import tarfile
import tempfile
import traceback
import time
import random

# Ensure the root project folder is in Python's search path
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..")))
from part1.models.GNBA import compute_closure, generate_initial_states
from part1.models.ltl_model import to_pnf
from part1.models.petrinet import parse_pnml_file, parse_property_xml, get_petri_product_successors_lazy
from part1.tools.nested_dfs import nested_dfs


def run_petri_checker(pnml_path, property_xml_path):
    net = parse_pnml_file(pnml_path)[0]
    parsed_properties = parse_property_xml(net, property_xml_path)
    results = []

    for prop_id, props_list, ltl_root_node in parsed_properties:
        gc.collect()  # make sure the garbage is collected from the previous run to safe memory

        dag = ltl_root_node.dag
        root_id = ltl_root_node.node_id
        negated_root = dag.make('~', root_id)
        pnf_root = to_pnf(dag, negated_root)
        closure = compute_closure(dag, pnf_root)

        # 2. Extract 'Until' formulas for finding acceptance states
        until_formulas = [nid for nid in closure if dag._nodes[nid][0] == 'U']
        k = len(until_formulas) if until_formulas else 1

        # 3. Generate Structural Initials for NBA
        structural_initials = [(s, 1) for s in generate_initial_states(dag, closure, pnf_root)]

        # 4. Build the dictionary of lambdas for acceptance sets
        gnba_acc_sets = {}
        if not until_formulas:
            # Trivial case: unconditionally accepting
            gnba_acc_sets[1] = lambda s: True
        else:
            for layer_idx, u_nid in enumerate(until_formulas, start=1):
                r_nid = dag._nodes[u_nid][2]
                # Make lambda's with the acceptence condition
                gnba_acc_sets[layer_idx] = lambda s, u=u_nid, r=r_nid: u not in s or r in s

        # 5. Generate the Petri net specific engine and initial product states
        product_successor_engine = get_petri_product_successors_lazy(net, props_list)
        product_initials = [(net.initial, init_nba) for init_nba in structural_initials]

        # 6. start the DFS and time it
        start = time.perf_counter()
        is_violating, witness = nested_dfs(
            dag, pnf_root, closure, gnba_acc_sets, k,
            get_successors_fn=product_successor_engine,
            initial_states_override=product_initials
        )
        elapsed = time.perf_counter() - start

        results.append({
            "id": prop_id,
            "status": "VIOLATED" if is_violating else "SATISFIED",
            "time": elapsed,
            "trace_length": len(witness) if witness else 0,
        })

        if is_violating:
            print(
                f"[FAIL] {prop_id} "
                f"(time={elapsed:.3f}s, counterexample={len(witness)} states)"
            )
        else:
            print(
                f"[ OK ] {prop_id} "
                f"(time={elapsed:.3f}s)"
            )

    print("\n" + "=" * 70)
    print("Verification Summary")
    print("=" * 70)

    satisfied = sum(r["status"] == "SATISFIED" for r in results)
    violated = len(results) - satisfied
    total_time = sum(r["time"] for r in results)

    print(f"Total properties : {len(results)}")
    print(f"Satisfied        : {satisfied}")
    print(f"Violated         : {violated}")
    print(f"Total runtime    : {total_time:.3f} s\n")

    print("{:<20} {:<12} {:>10} {:>12}".format(
        "Property", "Status", "Time(s)", "Trace Len"
    ))
    print("-" * 70)

    for r in results:
        print("{:<20} {:<12} {:>10.3f} {:>12}".format(
            str(r["id"]),
            r["status"],
            r["time"],
            r["trace_length"]
        ))


def diagnostic_worker():
    """
    This function holds the actual logic that runs inside the heavy-duty thread.
    """
    base_dir = os.path.dirname(os.path.abspath(__file__))
    inputs_dir = os.path.abspath(os.path.join(
        base_dir, "..", "inputs", "23_archive", "INPUTS-2023"
    ))

    print("=" * 60)
    archive_files = [
        f for f in os.listdir(inputs_dir)
        if (f.endswith('.tgz')) and "-COL-" not in f
    ]
    # selected_archive = random.choice(archive_files)
    selected_archive = "Peterson-PT-2.tgz"
    archive_path = os.path.join(inputs_dir, selected_archive)
    print(f"Input file: '{selected_archive}'")

    with tempfile.TemporaryDirectory() as temp_dir:
        try:
            with tarfile.open(archive_path, "r:gz") as tar:
                tar.extractall(path=temp_dir)
        except Exception as e:
            print(f"Extraction of input failed: {e}")
            return

        target_path = temp_dir
        for root, dirs, files in os.walk(temp_dir):
            if "model.pnml" in files:
                target_path = root
                break

        pnml_file = os.path.join(target_path, "model.pnml")
        property_file = os.path.join(target_path, "LTLFireability.xml")
        if not os.path.exists(property_file):
            property_file = os.path.join(target_path, "LTLCardinality.xml")

        if os.path.exists(pnml_file) and os.path.exists(property_file):
            print(f"Using Specs: {os.path.basename(property_file)}")

            try:
                run_petri_checker(pnml_file, property_file)
            except Exception as e:
                print(f"Verification execution failed due to runtime error: {e}")
                traceback.print_exc()
        else:
            print(f" Error: Could not locate 'model.pnml' or an LTL XML specification file.")


def main():
    # 1. Set the recursion limit higher required for deep DFS recursion
    sys.setrecursionlimit(50000)
    # 2. Use a thread so it can have more memory
    threading.stack_size(64 * 1024 * 1024)
    checker_thread = threading.Thread(target=diagnostic_worker)
    checker_thread.start()
    checker_thread.join()


if __name__ == "__main__":
    main()
