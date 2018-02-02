----------------------------- MODULE HourClock -----------------------------

EXTENDS Integers

VARIABLES hr

Init == hr \in 1..12

Next == hr' = IF hr # 12 THEN hr + 1 ELSE 1

Spec == Init /\ [][Next]_hr

-----------------------------------------------------------------------------
THEOREM Spec => []Init
=============================================================================
\* Modification History
\* Last modified Thu Feb 01 16:25:02 CET 2018 by jordy
\* Created Thu Feb 01 14:22:35 CET 2018 by jordy
