from collections import deque


class StateSpaceExplorer:
    def __init__(self, model):
        self.model = model

    def bfs(self):
        # this returns all visited states and deadlock states.

        visited = set()
        queue = deque()
        deadlocks = []

        for state in self.model.initial_states():
            visited.add(state)
            queue.append(state)

        while queue:
            state = queue.popleft()
            has_successor = False
            for _label, new_state in self.model.successors(state):

                has_successor = True

                if new_state not in visited:
                    visited.add(new_state)
                    queue.append(new_state)

            if not has_successor:
                deadlocks.append(state)

        return visited, deadlocks