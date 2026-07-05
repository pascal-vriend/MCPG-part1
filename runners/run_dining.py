# Ensure the root project folder is in Python's search path
import os
import sys
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..")))

from part1.tools.explorer import StateSpaceExplorer
from part1.models.dining_philosophers import DiningPhilosophers


variants = ['LEFT_FIRST', 'ARBITRARY', 'MIXED']
philosophers = [2, 3, 4, 5, 6]


for N in philosophers:
    print(f"\nN = {N}")

    for variant in variants:
        model = DiningPhilosophers(N, variant)

        explorer = StateSpaceExplorer(model)

        visited, deadlocks = explorer.bfs()

        print(
            f"{variant:12}"
            f" states={len(visited):5}"
            f" deadlocks={len(deadlocks):5}"
        )