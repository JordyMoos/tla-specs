-------------------------- MODULE AsynchInterface --------------------------
EXTENDS Integers

CONSTANT Data
VARIABLES val, rdy, ack


TypeInvariant == /\ val \in Data
                 /\ rdy \in {0, 1}
                 /\ ack \in {0, 1}


Init == /\ val \in Data
        /\ rdy \in {0, 1}
        /\ ack = rdy


Send == /\ rdy = ack
        /\ val' \in Data
        /\ rdy' = 1 - rdy
        /\ UNCHANGED ack


Rcv == /\ rdy # ack
       /\ ack' = 1 - ack
       /\ UNCHANGED <<val, rdy>>


Next == Send \/ Rcv


Spec == Init /\ [][Next]_<<val, rdy, ack>>

-----------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
=============================================================================
\* Modification History
\* Last modified Mon Feb 05 08:08:24 CET 2018 by jordy
\* Created Fri Feb 02 09:22:48 CET 2018 by jordy
