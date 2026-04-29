# CPSC 570: From Bugs to Proofs

**Advanced Topics in Computing** · Chapman University · Spring 2026

This repository contains coursework for CPSC 570, a course exploring formal methods for verifying software correctness -- from model checking concurrent systems to writing machine-checked proofs.

---

## Assignments

| # | Topic | Tools | Description |
|---|-------|-------|-------------|
| 1 | [Two-Phase Commit](Assignment1/) | TLA+ / PlusCal, TLC | Model and verify the 2PC distributed transaction protocol -- concurrency, liveness (fairness & termination), and safety (atomicity invariants) |
| 2 | [Red-Black Trees](Assignment2/) | Alloy Analyzer | Specify red-black tree invariants (coloring, black-height) and generate valid instances using constraint-based model finding |
| 3 | [LTL & Railroad Crossing](Assignment3/) | nuXmv, pen & paper | Prove LTL semantics, analyze transition systems, and model a railroad crossing controller with LTL/CTL verification and fairness |
| 4 | [CTL Exercises](Assignment4/) | pen & paper | Prove CTL semantic characterizations and analyze CTL properties on transition systems |
| 5 | [UPPAAL & Dafny](Assignment5/) | UPPAAL, Dafny | Verify real-time train-gate properties with timed automata; implement verified transactional inventory with pre/postconditions, loop invariants, and lemmas |
| 7 | [Lean 4 Exercises 1-3](Assignment7/) | Lean 4 | Types and terms (combinators), programs and theorems (AExp, predecessor, map), backward proofs (tactics, induction, classical logic) |
| 8 | [Lean 4 Homework 1-3](Assignment8/) | Lean 4 | B/S combinators, weakPeirce, snoc/sum, EM/DN/Peirce equivalence chain |

---

## Tools & Technologies

- **TLA+ / PlusCal** -- Formal specification language for modeling concurrent and distributed systems
- **TLC Model Checker** -- Exhaustive state-space exploration to verify temporal and safety properties
- **Alloy Analyzer** -- Constraint-based model finder for relational specifications
- **nuXmv** -- Symbolic model checker for CTL and LTL verification of finite-state systems
- **UPPAAL** -- Model checker for real-time systems using timed automata
- **Dafny** -- Verification-aware programming language with pre/postconditions and loop invariants
- **Lean 4** -- Dependently typed proof assistant and programming language

---

## Getting Started

### Prerequisites

- Java 16+
- [tla2tools.jar](https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar) (TLC model checker)
- [Alloy Analyzer](https://github.com/AlloyTools/org.alloytools.alloy/releases) (v6.x)
- [nuXmv](https://nuxmv.fbk.eu/download.html) (requires `gmp` -- install via `brew install gmp` on macOS)
- [UPPAAL](https://uppaal.org/) (GUI-based timed automata model checker)
- [Dafny](https://github.com/dafny-lang/dafny) (`brew install dafny` on macOS)
- [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) with `elan` and `lake`

### Running an Assignment

Each assignment directory contains its own README with specific instructions. Quick reference:

```bash
# TLA+ (Assignment 1)
java -cp tla2tools.jar pcal.trans <Module>.tla
java -jar tla2tools.jar -config <Config>.cfg <Module>

# Alloy (Assignment 2)
# Open .als file in Alloy Analyzer -> Execute -> Show

# nuXmv (Assignment 3)
nuXmv <Model>.smv

# UPPAAL (Assignment 5)
# Open .xml file in UPPAAL -> Verifier tab -> Run

# Dafny (Assignment 5)
dafny verify homework-transactions.dfy

# Lean 4 (Assignments 7-8)
lake build
```

---

## Author

**Ethan** · B.S. Computer Science, Chapman University '26
