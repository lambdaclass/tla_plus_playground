------------------------- MODULE DiemBFTOneProposer -------------------------
EXTENDS Naturals, Integers, FiniteSets


(***************************************************************************)
(*  Global Constants and Variables                                         *)
(***************************************************************************)
CONSTANTS    
    R,          \* Max number of rounds
    isLeader,   \* Function that tells if the node is selected as a leader in the round
    F           \* Number of Byzantine nodes

VARIABLES 
    round,      \* Current round
    roundStates,\* Mapping from round to the status of the current round
    votersPerRound

(***************************************************************************)
(* Helper Predicates                                                       *)
(***************************************************************************)
Rounds == 0..R
Voters == 0..(3*F)

MAXIMUM(S) == CHOOSE x \in S : \A y \in S : x >= y
MAX(a, b) == IF a > b THEN a ELSE b

ValidRoundStates == {"NOT_STARTED", "IGNORED", "PROPOSED"}
AllProposalMessages == [r: Rounds]
(***************************************************************************)
(* Formal Spec of Init State and Next State                                *)
(***************************************************************************)
NewProposal(proposalMsg) == /\ proposalMsg.r = round
                            /\ isLeader[round]
                            /\ roundStates' = [roundStates EXCEPT ![round] = "PROPOSED"]

AreMajority(V) == Cardinality(V) = (2*F + 1)

receiveVote(v, r) == /\ r >= round
                     /\ LET roundVoters == votersPerRound[r] \union {v} IN (
                        /\ votersPerRound' = [votersPerRound EXCEPT ![r] = roundVoters]
                        /\ (IF AreMajority(roundVoters) THEN
                            /\ round' = r + 1
                          ELSE
                            /\ round' = r)
                        )

Init == /\ round = 0
        /\ roundStates = [n \in Rounds \union {R+1} |-> "NOT_STARTED"]        
        /\ votersPerRound = [n \in Rounds \union {R+1} |-> {}]
        
Next == \/ /\ roundStates[round] = "NOT_STARTED"
           /\ \E proposalMsg \in AllProposalMessages : (
                /\  NewProposal(proposalMsg)
            )
        \/ /\ \E v \in Voters, r \in Rounds : receiveVote(v, r)
        \/ /\ ~isLeader[round]
           /\ roundStates' = [roundStates EXCEPT![round] = "IGNORED"]
           /\ round' = round + 1

\** Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)
TypeOK == /\ round \in Nat
          /\ \A r \in Rounds : roundStates[r] \in ValidRoundStates
          

=============================================================================
\* Modification History
\* Last modified Wed Jun 22 18:11:36 ART 2022 by lambda
\* Created Tue Jun 21 18:17:50 ART 2022 by lambda
