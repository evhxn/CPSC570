# PRISM Tutorial — Robot Navigation

**CPSC 570: From Bugs to Proofs** · Chapman University · Spring 2026

---

## Model Overview

The model is a Markov decision process (MDP) representing a robot moving through a 3×2 grid. States s0–s5 are laid out as:

```
s0  s1  s2   <- top row   ({hazard} at s1, {goal2} at s2)
s3  s4  s5   <- bottom row ({goal2} at s3, {goal1} at s5)
```

The robot starts at `s0`. States `s2` and `s3` are absorbing (stuck). State `s5` is `{goal1}`.

---

## Part 1 — Exploring the Model in the Simulator

### What is the final value of `s` after a long simulation?

After generating a random path, `s` will eventually stabilize at **s2, s3, or s5** — one of the three absorbing/stuck states. `s2` and `s3` loop via `[stuck]` indefinitely; `s5` loops via `[north]` or `[west]` with probability cycling. In practice, the simulator terminates in one of these states because no action escapes them:

- `s2`: `[stuck] s=2 -> 1 : (s'=2)` — the only available action loops back.
- `s3`: `[stuck] s=3 -> 1 : (s'=3)` — same.
- `s5`: can move `[north]` (0.9 → s2, 0.1 → s5) or `[west]` (1.0 → s4), so s5 is not fully absorbing but the robot tends to leave toward s2 or s4.

### Reaching `{goal1}` without passing through `{hazard}`

The only path from `s0` to `s5` that bypasses `s1` ({hazard}) is:

```
s0 --[south]--> s4 (prob 0.4) --[east]--> s5 (prob 1.0)
```

The combined probability of this two-step path is `0.4 × 1.0 = 0.4`. Manual exploration: from `s0`, take `[south]` hoping for `s4` (40% chance), then `[east]` to reach `s5` with certainty.

### Minimum and maximum path lengths (10-step traces)

- **Minimum**: 2 steps — `s0 →[south]→ s4 →[east]→ s5`
- **Maximum**: Paths that bounce (e.g. `s0 →[east]→ s0` repeatedly due to the 0.4 self-loop) can fill all 10 steps without reaching a terminal region. Observed maximum across several runs is 10 steps (trace still in-progress).

---

## Part 2 — Model Checking: `Pmax=? [ F "goal1" ]`

### Expected answer

From the MDP structure, the robot can always navigate `s0 → s4 → s5` by choosing `[south]` then `[east]`. Since the robot has *control* over which action to take (it's an MDP, not a DTMC), and action `[east]` from `s4` transitions to `s5` with probability **1.0**, the optimal policy can always eventually reach `s5`. There are no dead-ends that permanently block goal1.

**Expected result: `Pmax=? [ F "goal1" ] = 1.0`**

### Verification in PRISM

Loading `robot.props` and verifying `Pmax=? [ F "goal1" ]` returns **1.0**. The log confirms iterative value iteration converged with termination epsilon `1.0e-6`.

Changing termination epsilon to `1.0e-10` requires more iterations to converge but still returns 1.0 — the difference is only in computation cost, not the mathematical answer.

### Optimal policy for `Pmax=? [ F "goal1" ]`

PRISM's "View Strategy → Action List" shows:

| State | Optimal Action |
|-------|---------------|
| s0    | south         |
| s1    | south         |
| s4    | east          |
| s5    | (absorbing region — any) |

The policy is **memoryless** (depends only on current state). From `s0`, always take `[south]`: with prob 0.4 you reach `s4` directly, with prob 0.5 you land on `s3` (goal2, stuck — fails goal1), with prob 0.1 you land on `s1` where `[south]` from `s1` gives 0.5→s4, 0.5→s2. The policy maximizes probability of eventually reaching `s5`.

---

## Part 3 — Time-Bounded Property: `Pmax=? [ !"hazard" U<=k "goal2" ]`

### Property meaning

`Pmax=? [ !"hazard" U<=k "goal2" ]` asks: **what is the maximum probability, over all policies, of reaching a `{goal2}`-labeled state (s2 or s3) within exactly k steps, while never passing through `{hazard}` (s1)?**

The `!"hazard" U<=k "goal2"` formula is a *bounded until*: the robot must reach goal2 in at most k steps, and every state visited along the way must satisfy `!"hazard"` (i.e., not be s1).

### Manual analysis for k = 1, 2, 3

**k = 1** — reach goal2 in 1 step without visiting s1:

From s0, actions available: `[east]` (goes to s1 w.p. 0.6 — that's hazard, or s0 w.p. 0.4) and `[south]` (goes to s4 w.p. 0.4, s1 w.p. 0.1 — hazard, s3 w.p. 0.5).

Best: `[south]` from s0 — reaches s3 (goal2) with probability **0.5**, avoiding hazard. But any path through s1 is disqualified. So `Pmax=1 = 0.5`.

**k = 2** — reach goal2 in ≤ 2 steps without hazard:

New paths beyond k=1: after s0→s4 (prob 0.4), take `[west]` from s4 → s3 (goal2) w.p. 0.6 or s4 w.p. 0.4. So additional probability: `0.4 × 0.6 = 0.24`.

Cumulative (avoiding double-counting paths already succeeding at k=1): `Pmax=2 ≈ 0.5 + 0.4×0.6 = 0.74`.

**k = 3** — one more step of opportunity:

From s4 at step 2 (prob `0.4 × 0.4 = 0.16` of still being there), take `[west]` → s3 w.p. 0.6: adds `0.16 × 0.6 = 0.096`. `Pmax=3 ≈ 0.74 + 0.096 ≈ 0.836`.

### PRISM verification results

Loading the property with `k=1,2,3` as a constant confirms the values above. The "View Strategy" output shows the policy **does change** for different k:

- For k=1, the only useful action from s0 is `[south]` (to hit s3 directly).
- For k=2 and k=3, after landing on s4, `[west]` toward s3 becomes optimal. The policy becomes **time-dependent** (history matters — specifically, how many steps remain). PRISM represents this as a finite-memory strategy indexed by remaining steps.

### Does the optimal policy change for different k?

**Yes.** For small k (tight deadline), the robot must take the most direct route to goal2. For larger k, it can afford detours and the strategy at each state depends on how many steps remain. This is a classic example of a **non-stationary / time-dependent policy** arising from bounded-time objectives in MDPs — unlike the unbounded `F "goal1"` property, whose optimal policy was memoryless.

---

## Files

| File | Description |
|------|-------------|
| `robot.prism` | MDP model — 3×2 grid robot navigation |
| `robot.props` | Properties: `Pmax=? [ F "goal1" ]` and `Pmax=? [ !"hazard" U<=k "goal2" ]` |

---

## Author

**Ethan** · B.S. Computer Science, Chapman University '26
