import os
import sys
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..")))

from part1.tools.explorer import StateSpaceExplorer
from part1.models.petrinet import parse_pnml_file


def main():
    if len(sys.argv) > 1:
        path = sys.argv[1]
    else:
        path = "../inputs/philoslides.pnml"

    nets = parse_pnml_file(path)

    for i, net in enumerate(nets):
        print(f"\nNet {i}")

        explorer = StateSpaceExplorer(net)

        visited, deadlocks = explorer.bfs()

        print(f"Places     : {len(net.places)}")
        print(f"Transitions: {len(net.transitions)}")
        print()

        print(f"Reachable markings: {len(visited)}")
        print(f"Deadlocks         : {len(deadlocks)}")


if __name__ == "__main__":
    main()