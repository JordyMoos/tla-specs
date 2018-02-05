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


SSend(msg) ==
  /\ InChan ! Send(msg)
  /\ UNCHANGED <<out, queue>>


BufRcv ==
  /\ InChan ! Rcv
  /\ queue' = Append(queue, in.val)
  /\ UNCHANGED out


BufSend ==
  /\ queue # <<>>
  /\ OutChan ! Send(Head(queue))
  /\ queue' = Tail(queue)
  /\ UNCHANGED in


RRcv ==
  /\ OutChan ! Rcv
  /\ UNCHANGED <<in, queue>>


Next ==
    \/ \E msg \in Message : SSend(msg)
    \/ BufRcv
    \/ BufSend
    \/ RRcv


Spec == Init /\ [][Next]_<<in, out, queue>>

-----------------------------------------------------------------------------
THEOREM Spec => TypeInvariant
=============================================================================
\* Modification History
\* Last modified Mon Feb 05 09:07:08 CET 2018 by jordy
\* Created Fri Feb 02 11:27:30 CET 2018 by jordy
