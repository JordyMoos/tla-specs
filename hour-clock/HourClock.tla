----------------------------- MODULE HourClock -----------------------------

EXTENDS Integers

VARIABLES hr

Init == hr \in 1..12

Next == hr' = (hr % 12) + 1

Spec == Init /\ [][Next]_hr

-----------------------------------------------------------------------------
THEOREM Spec => []Init
=============================================================================
\* Modification History
\* Last modified Fri Feb 02 08:56:36 CET 2018 by jordy
\* Created Thu Feb 01 14:22:35 CET 2018 by jordy
