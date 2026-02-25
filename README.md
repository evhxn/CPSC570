# CPSC 570: From Bugs to Proofs

**Advanced Topics in Computing** · Chapman University · Spring 2026

This repository contains coursework for CPSC 570, a course exploring formal methods for verifying software correctness — from model checking concurrent systems to writing machine-checked proofs.

---

## Assignments

| # | Topic | Tools | Description |
|---|-------|-------|-------------|
| 1 | [Two-Phase Commit](Assignment1/) | TLA+ / PlusCal, TLC | Model and verify the 2PC distributed transaction protocol — concurrency, liveness (fairness & termination), and safety (atomicity invariants) |

> More assignments will be added as the course progresses.

---

## Tools & Technologies

- **TLA+ / PlusCal** — Formal specification language for modeling concurrent and distributed systems
- **TLC Model Checker** — Exhaustive state-space exploration to verify temporal and safety properties

---

## Getting Started

### Prerequisites

- Java 16+ 
- [tla2tools.jar](https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar) (TLC model checker)

### Running an Assignment

Each assignment directory contains `.tla` spec files and `.cfg` config files. To verify:

```bash
java -jar tla2tools.jar -config <ConfigFile>.cfg <ModuleName>
```

See individual assignment READMEs for specific instructions.

---

## Author

**Ethan** · B.S. Computer Science, Chapman University '26
