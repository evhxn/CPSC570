# Two-Phase Commit: TLC Observations Writeup

## Part 1: Concurrency

With `NumParticipants = 3`, TLC explored **610 states generated** and **297 distinct states**, completing a state graph search to **depth 17**. The state space captures every possible interleaving of the coordinator and 3 participant processes. Because each participant independently and nondeterministically votes YES or NO, there are 2^3 = 8 vote combinations. Participants can also vote in any order relative to one another, and the coordinator's steps interleave with all of them.

When participants vote in different orders, TLC explores interleavings where, for example, Participant 1 votes YES first while Participants 2 and 3 have not yet voted, or Participant 3 votes NO before anyone else votes. The coordinator's `C_CollectVotes` step is blocked (via `when AllVoted`) until every participant has cast a vote, so the order in which votes arrive does not affect the final decision — only the values matter. This confirms that 2PC correctly synchronizes despite arbitrary scheduling.

## Part 2: Liveness

Without fairness (`Spec` only), `LTermination` does not hold. TLC produces a counterexample: a behavior where some process (e.g., a participant) has a continuously enabled action but the stuttering step is taken forever instead. In TLA+ semantics, the specification allows infinite stuttering, meaning a process can be permanently starved even when it could make progress. The counterexample trace shows the system reaching a state where a participant could vote but never does, leaving the coordinator blocked at `C_CollectVotes` indefinitely.

With fairness (`LSpec`), `LTermination` holds. TLC verified this across all 297 distinct states with no errors. The weak fairness condition `WF_vars(ParticipantActions(self))` guarantees that if a participant's action is continuously enabled, it must eventually be taken. This eliminates the starvation scenarios and ensures every reachable behavior under `LSpec` eventually reaches the terminal state where all processes are "Done."

## Part 3: Safety

All three invariants — `TypeInvariant`, `Atomicity`, and `CoordinatorParticipantsAgree` — hold under `LSpec`. TLC explored 610 states (297 distinct) without finding any violation, confirming that 2PC guarantees atomicity: no execution can result in one participant being committed while another is aborted.

To test what happens when atomicity is broken, the `P_ApplyDecision` step can be modified so that a participant always commits regardless of the coordinator's decision (replacing the `if coordDecision = "commit"` check with an unconditional `partDecision[self] := "committed"`). TLC immediately finds a counterexample: in a trace where at least one participant votes NO, the coordinator decides "abort," the correctly-implemented participants set their state to "aborted," but the buggy participant sets its state to "committed." The counterexample trace pinpoints the exact interleaving where the Atomicity invariant is violated, demonstrating the power of model checking for finding bugs that would be extremely difficult to discover through testing alone.
