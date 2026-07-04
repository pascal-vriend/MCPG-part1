from part1.models.GNBA import compute_closure, generate_consistent_states
from part1.models.ltl_model import to_pnf
from part1.models.petrinet import parse_pnml_file, parse_property_xml, get_petri_product_successors_lazy
from part1.tools.nested_dfs import nested_dfs

import os
import sys
import tarfile
import tempfile
import random
import traceback

# Ensure the root project folder is in Python's search path
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..")))


def run_petri_checker(pnml_path, property_xml_path):
    net = parse_pnml_file(pnml_path)[0]
    parsed_properties = parse_property_xml(net, property_xml_path)

    for prop_id, props_list, ltl_root_node in parsed_properties:
        # FIX: Extract the actual DAG that contains all the parsed nodes
        dag = ltl_root_node.dag
        root_id = ltl_root_node.node_id
        negated_root = dag.make('~', root_id)
        pnf_root = to_pnf(dag, negated_root)
        # Compute the explicit closure and layers needed for the search
        closure = compute_closure(dag, pnf_root)
        until_formulas = [nid for nid in closure if dag._nodes[nid][0] == 'U']
        k = len(until_formulas) if until_formulas else 1

        print("🔮 Extracting starting configurations lazily...")

        # ─── OPTIMIZED: FILTER DIRECTLY DURING GENERATION ───────────────────
        # Instead of calling list(generate_consistent_states) which blows up memory,
        # we iterate through the generator dynamically and extract ONLY states containing our root.
        structural_initials = []
        for s in generate_consistent_states(dag, closure):
            if pnf_root in s:
                structural_initials.append((s, 1))

                # Safety valve: If we already have plenty of valid starting seeds,
                # we don't need to cycle through billions of combinations.
                if len(structural_initials) >= 500:
                    break

        # ────────────────────────────────────────────────────────────────────

        # Build the exact GNBA acceptance structure
        # Crucial: Treat gnba_acc_sets lazily inside your model checker transitions!
        # Since gnba_acc_sets[layer_idx] just checks if (u_nid not in s or r_nid in s),
        # we can completely avoid storing all_consistent by computing this dynamically.
        class LazyAcceptanceMapping:
            def __init__(self, until_formulas, dag):
                self.until_formulas = until_formulas
                self.dag = dag

            def __getitem__(self, layer_idx):
                # Return an object that evaluates the constraint on-the-fly via 'in' overrides
                class LazySetGuard:
                    def __init__(self, u_nid, r_nid):
                        self.u_nid = u_nid
                        self.r_nid = r_nid

                    def __contains__(self, s):
                        # The core GNBA condition: state does not have U, OR it has reached R
                        return self.u_nid not in s or self.r_nid in s

                if not self.until_formulas:
                    # Trivial case: unconditionally accepting
                    class TrivialSetGuard:
                        def __contains__(self, s): return True

                    return TrivialSetGuard()

                u_nid = self.until_formulas[layer_idx - 1]
                r_nid = self.dag._nodes[u_nid][2]
                return LazySetGuard(u_nid, r_nid)

        gnba_acc_sets = LazyAcceptanceMapping(until_formulas, dag)

        # Generate the engine function
        product_successor_engine = get_petri_product_successors_lazy(net, props_list)

        # Pair the initial marking with the initial structural configurations
        product_initials = [(net.initial, init_nba) for init_nba in structural_initials]

        # Invoke the DFS Checker
        is_violating, witness = nested_dfs(
            dag, pnf_root, closure, gnba_acc_sets, k,
            get_successors_fn=product_successor_engine,
            initial_states_override=product_initials
        )
        if is_violating:
            print(f"❌ Property {prop_id} is VIOLATED by the Petri Net!")
        else:
            print(f"✅ Property {prop_id} is SATISFIED by the Petri Net!")


def main():
    base_dir = os.path.dirname(os.path.abspath(__file__))
    inputs_dir = os.path.abspath(os.path.join(
        base_dir, "..", "inputs", "23_archive", "INPUTS-2023"
    ))

    print("=" * 60)
    print(f"📂 Scanning for Compressed MCC Benchmarks in:\n{inputs_dir}")
    print("=" * 60)

    if not os.path.exists(inputs_dir):
        print(f"❌ Error: The benchmark folder does not exist at:\n{inputs_dir}")
        return

    archive_files = [
        f for f in os.listdir(inputs_dir)
        if (f.endswith('.tgz') or f.endswith('.tar.gz')) and "-COL-" not in f
    ]

    if not archive_files:
        print("⚠ Warning: No compressed .tgz or .tar.gz model files found inside the directory.")
        return

    # 2. Select the first model archive file to test
    selected_archive = random.choice(archive_files)
    archive_path = os.path.join(inputs_dir, selected_archive)
    print(f"📦 Found Compressed Archive: '{selected_archive}'")

    # 3. Create a temporary folder to extract this model's contents into safely
    with tempfile.TemporaryDirectory() as temp_dir:
        print(f"🔄 Decompressing archive into temporary space...")
        try:
            with tarfile.open(archive_path, "r:gz") as tar:
                tar.extractall(path=temp_dir)
        except Exception as e:
            print(f"❌ Extraction failed: {e}")
            return

        # 4. Find where the files landed inside the temporary space
        # Some tars extract directly, others put everything in a nested subfolder
        target_path = temp_dir
        for root, dirs, files in os.walk(temp_dir):
            if "model.pnml" in files:
                target_path = root
                break

        pnml_file = os.path.join(target_path, "model.pnml")
        property_file = os.path.join(target_path, "LTLFireability.xml")
        if not os.path.exists(property_file):
            property_file = os.path.join(target_path, "LTLCardinality.xml")

        # 5. Run your verified engine loop
        if os.path.exists(pnml_file) and os.path.exists(property_file):
            print(f"📄 Extracted PNML Model successfully.")
            print(f"📄 Extracted Specs: {os.path.basename(property_file)}")
            print("\n🚀 Spawning Synchronized Product Space & Running Model Checker...")

            try:
                run_petri_checker(pnml_file, property_file)
            except Exception as e:
                print(f"💥 Verification execution failed due to runtime error: {e}")
                traceback.print_exc()
        else:
            print(f"❌ Error: Could not locate 'model.pnml' or an LTL XML specification file inside the archive.")


if __name__ == "__main__":
    main()
