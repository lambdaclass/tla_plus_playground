---------------------------- MODULE phil_problem ----------------------------
EXTENDS Integers
CONSTANT N
VARIABLES phiState, forkState

philos == 0..N-1
forks == 0..N-1

left(i) == (i + 1) % N
right(i) == (i + N - 1) % N

TypeOK == /\ phiState \in [ philos -> {"Thinking", "Eating"}]
          /\ forkState \in [ forks -> {"Hold", "Unhold"}]

Init == /\ phiState = [p \in philos |-> "Thinking"]
        /\ forkState = [f \in forks |-> "Unhold"]

leaveForksDown(i) == 
        /\ forkState' = [ forkState EXCEPT ![left(i)] = "Unhold", ![right(i)] = "Unhold"]

startThink(i) ==
    /\ phiState[i] = "Eating"
    /\ leaveForksDown(i)
    /\ phiState' = [ phiState EXCEPT ![i] = "Thinking" ]

startEat(i) == /\ phiState[i] = "Thinking"
          /\ phiState[left(i)] /= "Eating"
          /\ phiState[right(i)] /= "Eating"
          /\ forkState[left(i)] = "Hold"
          /\ forkState[right(i)] = "Hold"
          /\ phiState' = [ phiState EXCEPT ![i] = "Eating" ]
          /\ UNCHANGED forkState

holdLeftFork(i) ==
    /\ phiState[i] = "Thinking"
    /\ forkState[left(i)] = "Unhold"
    /\ forkState' = [ forkState EXCEPT ![left(i)] = "Hold" ]
    /\ UNCHANGED phiState

holdRightFork(i) ==
    /\ phiState[i] = "Thinking"
    /\ forkState[right(i)] = "Unhold"
    /\ forkState' = [ forkState EXCEPT ![right(i)] = "Hold" ]
    /\ UNCHANGED phiState

Next ==
  \E i \in philos : \/ startEat(i)
                    \/ startThink(i)
                    \/ holdLeftFork(i)
                    \/ holdRightFork(i)
Spec ==
  /\ Init
  /\ [] [ Next ]_<<phiState, forkState>>


=============================================================================
\* Modification History
\* Last modified Mon Jun 06 18:55:21 ART 2022 by ignacioavecilla
\* Created Mon Jun 06 16:37:09 ART 2022 by ignacioavecilla
