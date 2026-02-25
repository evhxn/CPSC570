# Two-Phase Commit: TLC Observations Writeup

## Part 1: Concurrency

With `NumParticipants = 3`, TLC explored **297 distinct states** (610 total generated) at a search depth of **17**. The state space captures every possible interleaving of the coordinator and 3 participant processes. Each participant nondeterministically votes "yes" or "no" (using `with v \in {"yes", "no"}`), giving 2^3 = 8 vote combinations. Participants can vote in any order, and the coordinator's steps interleave with all of them.

The coordinator blocks at `Decide` (via `when AllVoted`) until every participant has cast a vote, so the order of votes doesn't affect the final decision — only the values matter. In the `ReceiveDecision` step, the `either/or` construct ensures participants can only commit if they voted "yes" AND the coordinator committed, or abort if the coordinator aborted. TLC confirms no errors across all interleavings.

## Part 2: Liveness

Without fairness (`Spec` only), `LTermination` **does not hold**. TLC produces a counterexample showing a behavior where a process (e.g., a participant) has a continuously enabled action but stutters forever. The system reaches a state where a participant could vote but never does, leaving the coordinator blocked at `Decide` indefinitely. This isn't a protocol bug — it's the absence of a progress assumption.

With fairness (`LSpec`), `LTermination` **holds**. TLC verified this across all 297 distinct states with no errors. Weak fairness (`WF_vars`) is sufficient here because once a participant's `Vote` or `ReceiveDecision` action becomes enabled, it stays continuously enabled until taken — the enabling condition doesn't flicker on and off. Therefore strong fairness is not needed.

## Part 3: Safety

All three invariants hold under `LSpec`:

- **TypeInvariant:** `coordPhase` stays within `{"idle", "waiting", "committed", "aborted", "done"}`, `partPhase` stays within `{"idle", "voted", "committed", "aborted"}`, and `partVote` stays within `{"none", "yes", "no"}` across all reachable states.

- **Atomicity:** No reachable state has one participant in "committed" while another is in "aborted." This is the core safety guarantee of 2PC.

- **CoordinatorParticipantsAgree:** Whenever the coordinator is in "committed," no participant is "aborted," and vice versa.

TLC explored 610 states (297 distinct) and found no violations of any invariant.

To test what happens when atomicity is broken, the `ReceiveDecision` step can be modified to let a participant commit unconditionally (removing the `partVote[self] = "yes"` guard). TLC then finds a counterexample: a participant that voted "no" still ends up "committed" while another participant correctly aborts, violating the Atomicity invariant. The counterexample trace pinpoints the exact interleaving that causes the split outcome.
