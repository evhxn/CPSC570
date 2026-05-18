# Assignment 9 — Rocq Extraction & PRISM Robot Navigation

**CPSC 570: From Bugs to Proofs** · Chapman University · Spring 2026

---

## Part 1 — Rocq Extraction to Haskell

Extends `tutorial_02_extraction_haskell.v` with three new components:

- **Part 1:** `count_items` (recursive list length over `line_item`) and a proof that counting distributes over append (`count_items_app`)
- **Part 2:** `quantity_is_positive` and `all_quantities_positive` (boolean checkers) with a proof that the check distributes over append (`all_quantities_positive_app`)
- **Part 3:** `homework_summary_of_order` — a record combining the homework functions with verified tutorial functions (`total_quantity`, `validate_order`, `order_has_rush_fee`), extracted to Haskell

### Files

| File | Description |
|------|-------------|
| `hw_extraction_haskell.v` | Completed homework — all `Admitted` replaced with definitions and proofs |
| `HomeworkExtraction.hs` | Generated Haskell — produced by `rocq compile` |

### Running

```bash
rocq compile tutorial_02_extraction_haskell.v -output-directory .
rocq compile hw_extraction_haskell.v -output-directory .
```

Compiling produces `HomeworkExtraction.hs`. Functions to identify in the output: `count_items`, `order_item_count`, `all_quantities_positive`, `homework_summary_of_order`.

---

## Part 2 — PRISM Tutorial: Robot Navigation

Worked through the [PRISM robot navigation tutorial](https://www.prismmodelchecker.org/tutorial/) using the 3×2 grid MDP.

### Files

| File | Description |
|------|-------------|
| `robot.prism` | MDP model (download from tutorial link) |
| `robot.props` | Properties for model checking |
| `prism_robot_navigation_writeup.md` | Full written answers to all tutorial tasks |

### Key results

| Property | Result |
|----------|--------|
| `Pmax=? [ F "goal1" ]` | **1.0** — optimal policy always reaches goal1 |
| `Pmax=? [ !"hazard" U<=1 "goal2" ]` | **0.5** |
| `Pmax=? [ !"hazard" U<=2 "goal2" ]` | **≈ 0.74** |
| `Pmax=? [ !"hazard" U<=3 "goal2" ]` | **≈ 0.836** |

The unbounded goal 1 policy is **memoryless**. The bounded goal 2 policy is **time-dependent**; it changes with the remaining step budget.

### Running

```bash
# Launch PRISM GUI
bin/xprism

# Load model: Model > Open model > robot.prism
# Load properties: Properties > Open properties list > robot.props
# Right-click property > Verify
# For strategy: Strategies > Generate Strategy, then View Strategy > Action List
```

---

## Author

**Ethan** · B.S. Computer Science, Chapman University '26
