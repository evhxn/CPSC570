# CPSC 570: From Bugs to Proofs

**Advanced Topics in Computing** · Chapman University · Spring 2026

This repository contains coursework for CPSC 570, a course exploring formal methods for verifying software correctness — from model checking concurrent systems to writing machine-checked proofs.

---

## Assignments

| # | Topic | Tools | Description |
|---|-------|-------|-------------|
| 1 | [Two-Phase Commit](Assignment1/) | TLA+ / PlusCal, TLC | Model and verify the 2PC distributed transaction protocol — concurrency, liveness (fairness & termination), and safety (atomicity invariants) |
| 2 | [Red-Black Trees](Assignment2/) | Alloy Analyzer | Specify red-black tree invariants (coloring, black-height) and generate valid instances using constraint-based model finding |
| 3 | [LTL & Railroad Crossing](Assignment3/) | nuXmv, pen & paper | Prove LTL semantics, analyze transition systems, and model a railroad crossing controller with LTL/CTL verification and fairness |

---

## Tools & Technologies

- **TLA+ / PlusCal** — Formal specification language for modeling concurrent and distributed systems
- **TLC Model Checker** — Exhaustive state-space exploration to verify temporal and safety properties
- **Alloy Analyzer** — Constraint-based model finder for relational specifications
- **nuXmv** — Symbolic model checker for CTL and LTL verification of finite-state systems

---

## Getting Started

### Prerequisites

- Java 16+
- [tla2tools.jar](https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar) (TLC model checker)
- [Alloy Analyzer](https://github.com/AlloyTools/org.alloytools.alloy/releases) (v6.x)
- [nuXmv](https://nuxmv.fbk.eu/download.html) (requires `gmp` library — install via `brew install gmp` on macOS)

### Running an Assignment

Each assignment directory contains its own README with specific instructions. Quick reference:

```bash
# TLA+ (Assignment 1)
java -cp tla2tools.jar pcal.trans <Module>.tla
java -jar tla2tools.jar -config <Config>.cfg <Module>

# Alloy (Assignment 2)
# Open .als file in Alloy Analyzer → Execute → Show

# nuXmv (Assignment 3)
nuXmv <Model>.smv
```

---

## Author

**Ethan** · B.S. Computer Science, Chapman University '26
