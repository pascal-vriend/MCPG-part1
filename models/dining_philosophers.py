class DiningPhilosophers:
    def __init__(self, N, variant='LEFT_FIRST'):
        self.N = N
        self.variant = variant

    def initial_state(self):
        # I use tuples because they are hashable and that is needed for the visited set in explorer
        return tuple('thinking' for _ in range(self.N))

    def successors(self, state):
        # Generate all successor states reachable in one step.
        # Yields: (action_label, new_state)
        # I used generators, so if a deadlock is found early, we do not have to compute all successors.

        N = self.N
        for i in range(N):
            phil = state[i]

            # Philosopher i uses:
            #   left fork  = i
            #   right fork = (i + 1) % N (that is one index to the right, and the last one 0)
            lf = i
            rf = (i + 1) % N

            if phil == 'thinking':
                if self.variant == 'LEFT_FIRST':

                    if not self.fork_is_taken(state, lf):
                        new = list(state)
                        new[i] = 'has_left'

                        yield (f'p{i}_pick_left', tuple(new))

                elif self.variant == 'ARBITRARY':
                    if not self.fork_is_taken(state, lf):
                        new = list(state)
                        new[i] = 'has_left'

                        yield (f'p{i}_pick_left', tuple(new))

                    if not self.fork_is_taken(state, rf):
                        new = list(state)
                        new[i] = 'has_right'

                        yield (f'p{i}_pick_right', tuple(new))

                elif self.variant == 'MIXED':
                    if i == 0:
                        if not self.fork_is_taken(state, rf):
                            new = list(state)
                            new[i] = 'has_right'

                            yield (f'p{i}_pick_right', tuple(new))

                    else:

                        if not self.fork_is_taken(state, lf):
                            new = list(state)
                            new[i] = 'has_left'

                            yield (f'p{i}_pick_left', tuple(new))

            elif phil == 'has_left':

                if not self.fork_is_taken(state, rf):
                    new = list(state)
                    new[i] = 'eating'

                    yield (f'p{i}_pick_right', tuple(new))

            elif phil == 'has_right':

                if not self.fork_is_taken(state, lf):
                    new = list(state)
                    new[i] = 'eating'

                    yield (f'p{i}_pick_left', tuple(new))

            elif phil == 'eating':

                new = list(state)
                new[i] = 'thinking'

                yield (f'p{i}_done_eating', tuple(new))

    def initial_states(self):
        yield self.initial_state()

    def fork_is_taken(self, state, fork_idx):
        owner_left = fork_idx
        if state[owner_left] in ('has_left', 'eating'):
            return True
        owner_right = (fork_idx - 1) % self.N
        if state[owner_right] in ('has_right', 'eating'):
            return True
        return False
