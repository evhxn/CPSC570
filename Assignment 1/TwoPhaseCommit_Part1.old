----------------------------- MODULE TwoPhaseCommit_Part1 -----------------------------
(*
  Part 1: Concurrency
  
  HOMEWORK: Model the concurrent structure of Two-Phase Commit (2PC).
  
  Protocol overview:
  - Phase 1 (Prepare): Coordinator sends PREPARE to all participants.
      Each participant votes YES or NO.
  - Phase 2 (Decide): Coordinator collects votes.
      If ALL voted YES -> COMMIT. Otherwise -> ABORT.
      Participants receive the decision and update their state.
  
  YOUR TASK:
  1. Complete the Coordinator process:
     - SendPrepare: transition coordPhase from "idle" to "waiting"
     - Decide: wait until all participants have voted, then commit or abort
     - Finish: wait until all participants received the decision, then set "done"
  
  2. Complete the Participant process:
     - Vote: when the coordinator is waiting, nondeterministically vote "yes" or "no"
     - ReceiveDecision: receive commit (if voted yes and coordinator committed)
       or abort (if coordinator aborted)
  
  HINTS:
  - Use `when` to block until a condition holds
  - Use `with v \in {"yes", "no"} do ... end with` for nondeterministic choice
  - Use `either ... or ... end either` for branching on the decision
  - The helpers AllVoted, AllYes, AllDecided are provided for you
*)
EXTENDS Integers

CONSTANT NumParticipants

ASSUME NumParticipants \in 2..5

Coord == 0
Participants == 1..NumParticipants

(*--algorithm TwoPhaseCommit

variables
    (* coordPhase: "idle" -> "waiting" -> "committed"/"aborted" -> "done" *)
    coordPhase = "idle",
    (* partPhase: "idle" -> "voted" -> "committed"/"aborted" *)
    partPhase = [p \in Participants |-> "idle"],
    (* partVote: "none" -> "yes"/"no" *)
    partVote = [p \in Participants |-> "none"];

define
    AllVoted == \A p \in Participants: partPhase[p] # "idle"
    AllYes == \A p \in Participants: partVote[p] = "yes"
    AllDecided == \A p \in Participants: partPhase[p] \in {"committed", "aborted"}
end define;

fair process Coordinator = Coord
begin
    SendPrepare:
        when coordPhase = "idle";
        coordPhase := "waiting";
    Decide:
        when coordPhase = "waiting" /\ AllVoted;
        if AllYes then
            coordPhase := "committed";
        else
            coordPhase := "aborted";
        end if;
    Finish:
        when coordPhase \in {"committed", "aborted"} /\ AllDecided;
        coordPhase := "done";
end process;

fair process Participant \in Participants
begin
    Vote:
        when partPhase[self] = "idle" /\ coordPhase = "waiting";
        with v \in {"yes", "no"} do
            partVote[self] := v;
            partPhase[self] := "voted";
        end with;
    ReceiveDecision:
        either
            when partVote[self] = "yes" /\ coordPhase = "committed";
            partPhase[self] := "committed";
        or
            when coordPhase = "aborted";
            partPhase[self] := "aborted";
        end either;
end process;

end algorithm;*)
=============================================================================
