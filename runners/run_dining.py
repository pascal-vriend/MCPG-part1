from part1.tools.explorer import StateSpaceExplorer
from part1.models.dining_philosophers import DiningPhilosophers


variants = ['LEFT_FIRST', 'ARBITRARY', 'MIXED']
#variants = ['LEFT_FIRST']
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