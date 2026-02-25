--------------------------- MODULE TwoPhaseCommit_Part2 ---------------------------
(***************************************************************************)
(* Two-Phase Commit — Part 2: Liveness                                     *)
(* Adds fairness conditions so the protocol is guaranteed to terminate.    *)
(***************************************************************************)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT NumParticipants

Participants == 1..NumParticipants

(***************************************************************************)
(* --algorithm TwoPhaseCommit {

    variables
        coordPhase   = "init",
        coordDecision = "none",
        partPhase    = [p \in Participants |-> "init"],
        partVote     = [p \in Participants |-> "none"],
        partDecision = [p \in Participants |-> "none"],
        coordMsg     = "none",
        partVoteCount = 0,
        partAckCount  = 0;

    define {
        AllVoted    == \A p \in Participants : partVote[p] /= "none"
        AllYes      == \A p \in Participants : partVote[p] = "yes"
        AllDecided  == \A p \in Participants : partPhase[p] = "decided"
    }

    fair process (Coordinator = 0)
    {
        C_SendPrepare:
            coordMsg   := "prepare";
            coordPhase := "waiting";

        C_CollectVotes:
            when AllVoted;
            if (AllYes) {
                coordDecision := "commit";
            } else {
                coordDecision := "abort";
            };

        C_SendDecision:
            if (coordDecision = "commit") {
                coordMsg := "commit";
            } else {
                coordMsg := "abort";
            };
            coordPhase := "decided";

        C_WaitAcks:
            when AllDecided;
    }

    fair process (Participant \in Participants)
    {
        P_WaitPrepare:
            when coordMsg = "prepare";
            partPhase[self] := "voting";

        P_Vote:
            either {
                partVote[self] := "yes";
            } or {
                partVote[self] := "no";
            };

        P_WaitDecision:
            when coordPhase = "decided";

        P_ApplyDecision:
            if (coordDecision = "commit") {
                partDecision[self] := "committed";
            } else {
                partDecision[self] := "aborted";
            };
            partPhase[self] := "decided";
    }
}
*)

\* BEGIN TRANSLATION
VARIABLES coordPhase, coordDecision, partPhase, partVote, partDecision,
          coordMsg, partVoteCount, partAckCount, pc

vars == << coordPhase, coordDecision, partPhase, partVote, partDecision,
           coordMsg, partVoteCount, partAckCount, pc >>

ProcSet == {0} \cup (Participants)

Init == /\ coordPhase = "init"
        /\ coordDecision = "none"
        /\ partPhase = [p \in Participants |-> "init"]
        /\ partVote = [p \in Participants |-> "none"]
        /\ partDecision = [p \in Participants |-> "none"]
        /\ coordMsg = "none"
        /\ partVoteCount = 0
        /\ partAckCount = 0
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "C_SendPrepare"
                                        [] self \in Participants -> "P_WaitPrepare"]

(* define block *)
AllVoted    == \A p \in Participants : partVote[p] /= "none"
AllYes      == \A p \in Participants : partVote[p] = "yes"
AllDecided  == \A p \in Participants : partPhase[p] = "decided"

\* Coordinator actions
C_SendPrepare == /\ pc[0] = "C_SendPrepare"
                 /\ coordMsg'   = "prepare"
                 /\ coordPhase' = "waiting"
                 /\ pc' = [pc EXCEPT ![0] = "C_CollectVotes"]
                 /\ UNCHANGED << coordDecision, partPhase, partVote,
                                  partDecision, partVoteCount, partAckCount >>

C_CollectVotes == /\ pc[0] = "C_CollectVotes"
                  /\ AllVoted
                  /\ IF AllYes
                     THEN /\ coordDecision' = "commit"
                     ELSE /\ coordDecision' = "abort"
                  /\ pc' = [pc EXCEPT ![0] = "C_SendDecision"]
                  /\ UNCHANGED << coordPhase, partPhase, partVote,
                                   partDecision, coordMsg, partVoteCount, partAckCount >>

C_SendDecision == /\ pc[0] = "C_SendDecision"
                  /\ IF coordDecision = "commit"
                     THEN /\ coordMsg' = "commit"
                     ELSE /\ coordMsg' = "abort"
                  /\ coordPhase' = "decided"
                  /\ pc' = [pc EXCEPT ![0] = "C_WaitAcks"]
                  /\ UNCHANGED << coordDecision, partPhase, partVote,
                                   partDecision, partVoteCount, partAckCount >>

C_WaitAcks == /\ pc[0] = "C_WaitAcks"
              /\ AllDecided
              /\ pc' = [pc EXCEPT ![0] = "Done"]
              /\ UNCHANGED << coordPhase, coordDecision, partPhase, partVote,
                               partDecision, coordMsg, partVoteCount, partAckCount >>

Coordinator == C_SendPrepare \/ C_CollectVotes \/ C_SendDecision \/ C_WaitAcks

\* Participant actions
P_WaitPrepare(self) == /\ pc[self] = "P_WaitPrepare"
                       /\ coordMsg = "prepare"
                       /\ partPhase' = [partPhase EXCEPT ![self] = "voting"]
                       /\ pc' = [pc EXCEPT ![self] = "P_Vote"]
                       /\ UNCHANGED << coordPhase, coordDecision, partVote,
                                        partDecision, coordMsg, partVoteCount, partAckCount >>

P_Vote(self) == /\ pc[self] = "P_Vote"
                /\ \/ /\ partVote' = [partVote EXCEPT ![self] = "yes"]
                   \/ /\ partVote' = [partVote EXCEPT ![self] = "no"]
                /\ pc' = [pc EXCEPT ![self] = "P_WaitDecision"]
                /\ UNCHANGED << coordPhase, coordDecision, partPhase,
                                 partDecision, coordMsg, partVoteCount, partAckCount >>

P_WaitDecision(self) == /\ pc[self] = "P_WaitDecision"
                        /\ coordPhase = "decided"
                        /\ pc' = [pc EXCEPT ![self] = "P_ApplyDecision"]
                        /\ UNCHANGED << coordPhase, coordDecision, partPhase, partVote,
                                         partDecision, coordMsg, partVoteCount, partAckCount >>

P_ApplyDecision(self) == /\ pc[self] = "P_ApplyDecision"
                         /\ IF coordDecision = "commit"
                            THEN /\ partDecision' = [partDecision EXCEPT ![self] = "committed"]
                            ELSE /\ partDecision' = [partDecision EXCEPT ![self] = "aborted"]
                         /\ partPhase' = [partPhase EXCEPT ![self] = "decided"]
                         /\ pc' = [pc EXCEPT ![self] = "Done"]
                         /\ UNCHANGED << coordPhase, coordDecision, partVote,
                                          coordMsg, partVoteCount, partAckCount >>

Participant(self) == \/ P_WaitPrepare(self)
                     \/ P_Vote(self)
                     \/ P_WaitDecision(self)
                     \/ P_ApplyDecision(self)

(***************************************************************************)
(* Next-state relation (no fairness — used as baseline)                    *)
(***************************************************************************)
Next == \/ Coordinator
        \/ (\E self \in Participants : Participant(self))
        \/ ((\A self \in ProcSet : pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Part 2 additions: Fairness and Termination                              *)
(***************************************************************************)

\* Group all coordinator actions into one disjunction
CoordinatorActions == C_SendPrepare \/ C_CollectVotes \/ C_SendDecision \/ C_WaitAcks

\* Group all participant actions for a given participant
ParticipantActions(self) == P_WaitPrepare(self) \/ P_Vote(self)
                            \/ P_WaitDecision(self) \/ P_ApplyDecision(self)

\* Liveness specification: Spec + weak fairness on every process's actions
\* Weak fairness (WF) says: if an action is continuously enabled, it must
\* eventually be taken. This prevents stuttering / starvation.
LSpec == Spec
         /\ WF_vars(CoordinatorActions)
         /\ \A self \in Participants : WF_vars(ParticipantActions(self))

\* Termination: eventually all processes reach the "Done" state
LTermination == <>(\A self \in ProcSet : pc[self] = "Done")

=============================================================================
