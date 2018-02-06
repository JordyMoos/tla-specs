----------------------------- MODULE InnerFIFO -----------------------------
EXTENDS Naturals, Sequences

CONSTANT Message
VARIABLES in, out, q

InChan == INSTANCE Channel WITH Data <- Message, chan <- in
OutChan == INSTANCE Channel WITH Data <- Message, chan <- out


TypeInvariant ==
  /\ InChan ! TypeInvariant
  /\ OutChan ! TypeInvariant
  /\ q \in Seq(Message)
    
-----------------------------------------------------------------------------

Init ==
  /\ InChan ! Init
  /\ OutChan ! Init
  /\ q = <<>>


SSend(msg) ==
  /\ InChan ! Send(msg)
  /\ UNCHANGED <<out, q>>


BufRcv ==
  /\ InChan ! Rcv
  /\ q' = Append(q, in.val)
  /\ UNCHANGED out


BufSend ==
  /\ q # <<>>
  /\ OutChan ! Send(Head(q))
  /\ q' = Tail(q)
  /\ UNCHANGED in


RRcv ==
  /\ OutChan ! Rcv
  /\ UNCHANGED <<in, q>>


Next ==
    \/ \E msg \in Message : SSend(msg)
    \/ BufRcv
    \/ BufSend
    \/ RRcv


Spec == Init /\ [][Next]_<<in, out, q>>

-----------------------------------------------------------------------------
THEOREM Spec => TypeInvariant
=============================================================================
\* Modification History
\* Last modified Tue Feb 06 17:49:15 CET 2018 by jordy
\* Created Fri Feb 02 11:27:30 CET 2018 by jordy
