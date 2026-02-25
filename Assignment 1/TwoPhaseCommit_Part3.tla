----------------------------- MODULE TwoPhaseCommit_Part3 -----------------------------
(*
  Part 3: Safety
  
  HOMEWORK: Add invariants to verify the core safety property of 2PC --
  atomicity: all participants commit or all abort. Never a split outcome.
  
  BACKGROUND:
  - A safety property says "something bad never happens."
  - An invariant is a state predicate that must hold in every reachable state.
  - TLC checks invariants at every state during model checking.
  
  YOUR TASK:
  1. Define TypeInvariant: all variables stay within their valid domains.
     - coordPhase is one of: "idle", "waiting", "committed", "aborted", "done"
     - partPhase maps each participant to one of: "idle", "voted", "committed", "aborted"
     - partVote maps each participant to one of: "none", "yes", "no"
  
  2. Define Atomicity: no participant is committed while another is aborted.
     (This is the core safety property of 2PC.)
  
  3. Define CoordinatorParticipantsAgree: the coordinator's decision is
     consistent with participant states. For example:
     - If coordinator committed, no participant should be in "aborted"
     - If coordinator aborted, no participant should be in "committed"
  
  4. Define Invariants as the conjunction of all three.
  
  HINTS:
  - Use \A p, q \in Participants for quantifying over pairs
  - Use ~ (negation) to express "it is never the case that..."
  - Use => (implication) for "if coordinator committed then ..."
  - A function type is written [Domain -> Range] in TLA+
  
  RUNNING TLC:
  - Check LSpec (from Part 2) as the specification
  - Add Invariants as an invariant to check
  - Add LTermination as a property to check
  - Set NumParticipants to 3
*)
EXTENDS TwoPhaseCommit_Part2

\* TypeInvariant: all variables stay within their valid domains
TypeInvariant ==
    /\ coordPhase \in {"idle", "waiting", "committed", "aborted", "done"}
    /\ partPhase \in [Participants -> {"idle", "voted", "committed", "aborted"}]
    /\ partVote \in [Participants -> {"none", "yes", "no"}]

\* Atomicity: no participant is committed while another is aborted
Atomicity ==
    ~(\E p, q \in Participants :
        /\ partPhase[p] = "committed"
        /\ partPhase[q] = "aborted")

\* CoordinatorParticipantsAgree: coordinator decision matches participant states
CoordinatorParticipantsAgree ==
    /\ (coordPhase = "committed") =>
           ~(\E p \in Participants : partPhase[p] = "aborted")
    /\ (coordPhase = "aborted") =>
           ~(\E p \in Participants : partPhase[p] = "committed")

\* Conjunction of all invariants (used in TLC config)
Invariants ==
    /\ TypeInvariant
    /\ Atomicity
    /\ CoordinatorParticipantsAgree

=============================================================================
