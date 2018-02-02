----------------------------- MODULE InnerFIFO -----------------------------
EXTENDS Naturals, Sequences

CONSTANT Message
VARIABLES in, out, queue

InChan == INSTANCE Channel WITH Data <- Message, chan <- in
OutChan == INSTANCE Channel WITH Data <- Message, chan <- out


TypeInvariant ==
  /\ InChan ! TypeInvariant
  /\ OutChan ! TypeInvariant
  /\ queue \in Seq(Message)
    
-----------------------------------------------------------------------------

Init ==
  /\ InChan ! Init
  /\ OutChan ! Init
  /\ queue = <<>>


SSend(msg) == TRUE


BufRcv == TRUE


BufSend == TRUE


RRcv == TRUE


Next ==
    \/ \E msg \in Message : SSend(msg)
    \/ BufRcv
    \/ BufSend
    \/ RRcv


=============================================================================
\* Modification History
\* Last modified Fri Feb 02 11:55:41 CET 2018 by jordy
\* Created Fri Feb 02 11:27:30 CET 2018 by jordy
