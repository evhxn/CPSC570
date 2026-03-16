# Railroad Crossing Controller: nuXmv Observations Writeup

## Part 1: Modeling

The safety property `AG safe` **passes**. The gate begins lowering when the train is `approaching`, completes lowering to `down` in one step, and the train must still pass through `near` before reaching `crossing`. This gives the gate enough time (the `near` state acts as a buffer). The gate stays `down` until the train is `leaving`, then transitions through `raising → up`.

The gate guards are ordered so that the first matching case wins: lowering is triggered by `gate = up & train = approaching`, and raising by `gate = down & train = leaving`. The default `TRUE : gate` keeps the gate in its current state otherwise (e.g., gate stays `up` when no train is present, gate stays `down` while the train is `near` or `crossing`).

## Part 2: LTL Specifications

All three LTL properties **pass**:

1. **Safety** `G (train = crossing -> gate = down)` — The gate is fully down before the train reaches crossing, guaranteed by the `near` buffer state.

2. **Response** `G (train = approaching -> F (gate = down))` — Once approaching, the train deterministically progresses through `approaching → near → crossing`. The gate starts lowering on `approaching` and is `down` by the next step, so `F (gate = down)` is satisfied.

3. **Gate progress** `G (gate = lowering -> X (gate = down))` — The gate transition from `lowering` unconditionally goes to `down` (the case `gate = lowering : down` has no additional guard). So in the very next state after `lowering`, the gate is always `down`.

## Part 3: CTL + Fairness

### Without FAIRNESS

To reproduce: comment out the `FAIRNESS (train = approaching)` line in `RailroadCrossing_Part3.smv` and re-run. The results are:

- **CTL 1 (Safety)** `AG safe` — **Passes.** Safety holds regardless of fairness since it only requires something bad never happens.
- **CTL 2 (Reachability)** `EF (train = crossing & gate = down)` — **Passes.** There exists at least one path where a train crosses with the gate down.
- **CTL 3 (Recovery)** `AG (EF (gate = up))` — **Passes.** From any state, there's always a path back to `gate = up`.
- **CTL 4 (Response)** `AG (approaching -> AF (gate = down))` — **Passes.** Once approaching, the train progresses deterministically, and the gate reaches `down` within one step.
- **CTL 5 (Gate progress)** `AG (lowering -> AX down)` — **Passes.** Same reasoning as LTL property 3.
- **BONUS** `AG (AF (train = crossing))` — **Fails.** The counterexample is the path where the train stays `absent` forever. The nondeterministic choice `{absent, approaching}` always picks `absent`, so `train = crossing` never holds and `AF (train = crossing)` is false on that path.

### With FAIRNESS (submitted version)

With `FAIRNESS (train = approaching)` uncommented (as in the submitted file), **all properties pass**, including the BONUS. The fairness constraint eliminates degenerate paths where the train never approaches. It requires that `train = approaching` holds infinitely often on any fair execution, modeling the realistic assumption that trains keep arriving. This is analogous to the mutex lecture demo where `FAIRNESS turn = 1` prevented starvation by ensuring each process gets a turn.

### Comparison: LTL vs CTL

The LTL property `G (train = crossing -> gate = down)` corresponds directly to the CTL property `AG safe`. Both express the same safety guarantee — the gate must be down whenever a train is crossing. The LTL version is checked over linear traces (one path at a time), while the CTL version quantifies over all paths explicitly with `A`. For safety properties like this one, they are equivalent.

For liveness, LTL's `G (train = approaching -> F (gate = down))` corresponds to CTL's `AG (train = approaching -> AF (gate = down))`. The key difference is that nuXmv checks LTL under implicit fairness, while CTL requires an explicit `FAIRNESS` declaration to get the same effect. This is why LTL liveness properties can pass even without a fairness line, while CTL liveness properties like the BONUS may fail without one.
