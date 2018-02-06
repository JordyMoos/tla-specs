----------------------------- MODULE FIFO -----------------------------------
CONSTANT Message
VARIABLES in, out


Inner(q) == INSTANCE InnerFIFO


Spec == \E q : Inner(q) ! Spec

-----------------------------------------------------------------------------
=============================================================================
\* Modification History
\* Last modified Tue Feb 06 17:55:07 CET 2018 by jordy
\* Created Tue Feb 06 17:49:15 CET 2018 by jordy
