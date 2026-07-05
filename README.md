# Part 1

This directory contains three runner scripts that demonstrate the different components of the project.

---

## Script 1 – Dining Philosophers State Exploration

Run:

```bash
python3 runners/run_dining.py
```

This script performs state-space exploration of the Dining Philosophers model for:

- Number of philosophers: **2, 3, 4, 5, and 6**
- Variants:
  - `LEFT_FIRST`
  - `ARBITRARY`
  - `MIXED`

The results are printed as a table containing the exploration statistics for each configuration.

To verify the correctness of the generated state spaces, run:

```bash
python3 runners/run_pnml.py
```

This script uses the same state space explorer as run_dining.py, but with the different successor function in petrinet.py

---

## Script 2 – Petri Net LTL Model Checker

**Recommended:** Run this script using **PyPy** for significantly better performance, since PyPy's JIT compiler speeds up the search algorithms.

Example:

```bash
C:\pypy\pypy.exe runners/run_petrinet_ltl_check.py
```

By default, the script verifies the model contained in:

```
Peterson-PT-2.tgz
```

To verify a different benchmark, change the `selected_archive` variable inside `run_petrinet_ltl_check.py`.

After execution, the script prints a summary indicating which LTL properties were satisfied or violated, together with the verification time for each property.

---

## Script 3 – LTL Verification Pipeline

Run:

```bash
python3 runners/run_ltl_check.py
```

This launches an interactive terminal interface where LTL formulas can be entered.

By default, the complete verification pipeline is executed:

```
LTL Formula
    ↓
Positive Normal Form (PNF)
    ↓
Generalized Büchi Automaton (GNBA)
    ↓
Büchi Automaton (NBA)
    ↓
Satisfiability Check
```

Whenever the GNBA or NBA is constructed, the automata are exported to the `outputs/` directory as both:

- **PNG images** for visualization
- **DOT files** for inspection or rendering with Graphviz

### Optional command-line arguments

Run only specific stages of the pipeline by typing this after the LTL formula:

| Argument | Description                                                                                        |
|----------|----------------------------------------------------------------------------------------------------|
| `--gnba` | Build only the GNBA and export it to `outputs/` as PNG and DOT files.                              |
| `--nba` | Build the GNBA, convert it to an NBA, and export both automata to `outputs/` as PNG and DOT files. |
| `--check` | Execute the complete satisfiability check without building the entire gnba or nba.                 |