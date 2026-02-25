# Homework: Two-Phase Commit in PlusCal / TLA+

## How to Run

### Prerequisites
- Java 16+ installed
- Download `tla2tools.jar` from https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar

### Command Line

Place `tla2tools.jar` in the same directory as the `.tla` and `.cfg` files, then run:

```bash
# Part 1: Concurrency
java -jar tla2tools.jar -config TwoPhaseCommit_Part1.cfg TwoPhaseCommit_Part1

# Part 2: Liveness (with fairness — LTermination should pass)
java -jar tla2tools.jar -config TwoPhaseCommit_Part2.cfg TwoPhaseCommit_Part2

# Part 3: Safety (invariants + liveness — all should pass)
java -jar tla2tools.jar -config TwoPhaseCommit_Part3.cfg TwoPhaseCommit_Part3
```

### VSCode (TLA+ Extension)

1. Install the **TLA+** extension by Markus Kuppe from the Extensions marketplace
2. Open any `.tla` file
3. Press `Ctrl+Shift+P` (or `Cmd+Shift+P` on Mac) → **"TLA+: Check model with TLC"**
4. TLC will use the matching `.cfg` file automatically

### TLA+ Toolbox (GUI)

1. File → Open Spec → select `TwoPhaseCommit_Part3.tla`
2. TLC Model Checker → New Model
3. Set constant: `NumParticipants = 3`
4. Behavior spec: `LSpec`
5. Invariants: `Invariants`
6. Properties: `LTermination`
7. Click Run

### Expected Results

All three parts should produce:

```
Model checking completed. No error has been found.
610 states generated, 297 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 17.
```

## Files

| File | Description |
|------|-------------|
| `TwoPhaseCommit_Part1.tla` | Concurrency — coordinator and participants as concurrent PlusCal processes |
| `TwoPhaseCommit_Part1.cfg` | TLC config for Part 1 (`Spec`, NumParticipants = 3) |
| `TwoPhaseCommit_Part2.tla` | Liveness — adds fairness (WF) and termination property |
| `TwoPhaseCommit_Part2.cfg` | TLC config for Part 2 (`LSpec` + `LTermination`) |
| `TwoPhaseCommit_Part3.tla` | Safety — adds TypeInvariant, Atomicity, CoordinatorParticipantsAgree |
| `TwoPhaseCommit_Part3.cfg` | TLC config for Part 3 (`LSpec` + `Invariants` + `LTermination`) |
| `writeup.md` | Observations from running TLC on each part |
