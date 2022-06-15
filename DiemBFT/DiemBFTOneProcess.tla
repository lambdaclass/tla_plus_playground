------------------------- MODULE DiemBFTOneProcess -------------------------
EXTENDS Naturals, Integers

(***************************************************************************)
(*  Global Constants and Variables                                         *)
(***************************************************************************)
CONSTANTS    
    R           \* Max number of rounds

VARIABLES 
    nodeState,  \* Mapping of a round r to the state of the proposal, 
                \* the states are defined in ValidRoundStates.
    round,      \* Current round
    QCs,        \* Set of received QCs
    latestTC

(***************************************************************************)
(* Helper Predicates                                                       *)
(***************************************************************************)
ValidRoundStates == {"UNSEEN", "PREVOTE", "PRECOMMIT", "COMMIT", "COMMITED", "TCed"}
Rounds == 0..R

MAXIMUM(S) == CHOOSE x \in S : \A y \in S : x >= y
MAX(a, b) == IF a > b THEN a ELSE b

AllQCs == [r: Rounds, prevQC: Rounds \union {-1}]
ExistsQC(r) == \E qc \in QCs : (qc.r = r)
AllTCs == [r: Rounds, highQCRound: SUBSET Rounds]

(***************************************************************************)
(* Formal Spec of Init State and Next State                                *)
(***************************************************************************)
RoundTCed(r) == IF r > 1
                THEN nodeState' = [nodeState EXCEPT![r] = "TCed", ![r-1] = "TCed", ![r-2] = "TCed", ![r+1] = "PREVOTE"]
                ELSE IF r > 0
                THEN nodeState' = [nodeState EXCEPT![r] = "TCed", ![r-1] = "TCed", ![r+1] = "PREVOTE"]
                ELSE nodeState' = [nodeState EXCEPT![r] = "TCed", ![r+1] = "PREVOTE"]

RoundReady(r) == nodeState' = [nodeState EXCEPT![r] = "PREVOTE"]
RoundPreVoted(r) == nodeState' = [nodeState EXCEPT![r] = "PRECOMMIT"]
RoundPreCommited(r) == nodeState' = [nodeState EXCEPT![r] = "COMMIT", ![r+1] = "PRECOMMIT"]
RoundCommited(r) == nodeState' = [nodeState EXCEPT![r] = "COMMITED", ![r+1] = "COMMIT", ![r+2] = "PRECOMMIT"]
      
NewQC(qc) == /\ qc.r >= round
             /\ (
                    \/ (qc.prevQC = -1 /\ qc.r = 0) 
                    \/ (round > 0 /\ ExistsQC(qc.prevQC) /\ qc.prevQC = round - 1)
                )  
             /\ qc \notin QCs
             /\ IF qc.r >= 2 /\ ExistsQC(qc.r-1) /\ ExistsQC(qc.r-2)
               THEN RoundCommited(qc.r-2)
               ELSE IF qc.r >= 1 /\ ExistsQC(qc.r-1)
               THEN RoundPreCommited(qc.r-1)
               ELSE RoundPreVoted(qc.r)
             /\ QCs' = QCs \union {qc}
             /\ UNCHANGED <<latestTC>>
             
NewTC(tc) == /\ tc.r >= round
             /\ latestTC' = tc.r
             /\ RoundTCed(tc.r)
             /\ UNCHANGED <<QCs>>
             
        
Init == /\ round = 0
        /\ QCs = {}
        /\ nodeState = [n \in Rounds \union {R+1} |-> "UNSEEN"]
        /\ latestTC = -1
        
Next == \/ \E qc \in AllQCs : (
                /\  NewQC(qc)
                /\  round' = qc.r + 1
            )
        \/ \E tc \in AllTCs : (
                /\ NewTC(tc)
                /\ round' = tc.r + 1
            )

Spec == Init /\ [][Next]_<<nodeState, round, QCs, latestTC>>

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)
TypeOK == /\ round \in Nat
          /\ QCs \subseteq [r: Rounds, prevQC: Rounds \union {-1}]
          /\ nodeState \in [Rounds \union {R+1} -> ValidRoundStates]
          /\ latestTC \in Rounds \union {-1}
          
=============================================================================
\* Modification History
\* Last modified Wed Jun 15 12:46:46 ART 2022 by lambda
\* Created Mon Jun 13 08:53:58 ART 2022 by lambda
