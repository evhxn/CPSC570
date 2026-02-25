# Homework: Two-Phase Commit in PlusCal / TLA+

## How to Run

### Prerequisites
- Java 16+
- Download [tla2tools.jar](https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar)

### Important: Translate PlusCal First

Part 1 contains PlusCal that must be translated to TLA+ before TLC can run. Parts 2 and 3 extend Part 1 via `EXTENDS`, so only Part 1 needs translation.

```bash
java -cp tla2tools.jar pcal.trans TwoPhaseCommit_Part1.tla
```

Or in VSCode: open `TwoPhaseCommit_Part1.tla` and press `Ctrl+T` (`Cmd+T` on Mac).

### Running TLC

```bash
# Part 1: Concurrency (basic model checking)
java -jar tla2tools.jar -config TwoPhaseCommit_Part1.cfg TwoPhaseCommit_Part1

# Part 2: Liveness (fairness + termination)
java -jar tla2tools.jar -config TwoPhaseCommit_Part2.cfg TwoPhaseCommit_Part2

# Part 3: Safety (invariants + liveness)
java -jar tla2tools.jar -config TwoPhaseCommit_Part3.cfg TwoPhaseCommit_Part3
```

### Expected Output (all three parts)

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
| `TwoPhaseCommit_Part2.tla` | Liveness — extends Part 1 with fairness (WF) and termination |
| `TwoPhaseCommit_Part2.cfg` | TLC config for Part 2 (`LSpec` + `LTermination`) |
| `TwoPhaseCommit_Part3.tla` | Safety — extends Part 2 with TypeInvariant, Atomicity, CoordinatorParticipantsAgree |
| `TwoPhaseCommit_Part3.cfg` | TLC config for Part 3 (`LSpec` + `Invariants` + `LTermination`) |
| `writeup.md` | Observations from running TLC on each part |
