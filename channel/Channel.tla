------------------------------ MODULE Channel ------------------------------
EXTENDS Integers

CONSTANT Data
VARIABLE chan

TypeInvariant == chan \in [val: Data, rdy: {0, 1}, ack: {0, 1}]
-----------------------------------------------------------------------------

Init ==
  /\ TypeInvariant
  /\ chan.ack = chan.rdy


Send(d) ==
  /\ chan.rdy = chan.ack
  /\ chan' = 
       [ chan EXCEPT
         !.val = d
       , !.rdy = 1 - @
       ]


Rcv ==
  /\ chan.rdy # chan.ack
  /\ chan' = [ chan EXCEPT !.ack = 1 - @ ]


Next == (\E d \in Data : Send(d)) \/ Rcv


Spec == Init /\ [][Next]_chan

-----------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
=============================================================================
\* Modification History
\* Last modified Fri Feb 02 10:38:45 CET 2018 by jordy
\* Created Fri Feb 02 10:13:28 CET 2018 by jordy
