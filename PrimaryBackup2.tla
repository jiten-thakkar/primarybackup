--------------------------- MODULE PrimaryBackup2 ---------------------------
EXTENDS Integers, TLC
CONSTANT N
ASSUME N \in Nat
Procs == 1..N
(*
--algorithm PB {
    variable timeOut = [i \in Procs |-> 1], pings = [i \in Procs |-> 0], 
            view = 0, primary = 0, backup = 0, pendingAck = FALSE, serverViewNum = [i \in Procs |-> 0];

        \* View Service
        fair process(vs = 0)
            { vs: while (TRUE) {
                tick: if(primary # 0) {
                        if(pendingAck = FALSE) {
                            if(timeOut[primary] = 1) {
                                if(backup # 0) {
                                    primary := backup;
                                    backup := 0;
                                    view := view + 1;
                                    pendingAck := TRUE;
                                }
                            }
                        }
                      };
                      if(backup # 0) {
                        if(timeOut[backup] = 1) {
                          e1: with (i = {j \in Procs : { y \in Procs : pings[j] >= pings[y]}}) {
                          if(timeOut[i] # 1) {
                            backup := i;
                            view := view + 1;
                            pendingAck := TRUE;
                          }
                          }
                        }
                      }
              }
            }
        
        \* servers
       fair process(p \in Procs)
           {  server: while(TRUE) {
                either timeOut[self] := 1;
                or {
                    p1: timeOut[self] := 0;
            pings[self] := pings[self] + 1;
            if(serverViewNum[self] = 0) {
                if(self = primary) {
                    primary := backup;
                    backup := 0;
                    view := view + 1;
                    pendingAck := TRUE;
                } else if(self = backup) {
                    backup := 0;
                }
            };
            if(pendingAck = TRUE) {
                if(self = primary) {
                    if(view = serverViewNum[self]) {
                        p2: pendingAck := FALSE;
                        p3: with (i = {j \in Procs: {y \in Procs: pings[j] >= pings[y]}}) {
                          if(timeOut[i] # 1) {
                            backup := i;
                            view := view + 1;
                            pendingAck := TRUE;
                          }
                          }
                    }
                }
            } else {
                if(primary = 0) {
                    p4: with (i = {j \in Procs: {y \in Procs : pings[j] >= pings[y]}}) {
                          if(timeOut[i] # 1) {
                            primary := i;
                            view := view + 1;
                            pendingAck := TRUE;
                          }
                        }
                } else if(backup = 0) {
                    p5: with (i = {j \in Procs : { y \in Procs : pings[j] >= pings[y]}}) {
                          if(timeOut[i] # 1) {
                            backup := i;
                            view := view + 1;
                            pendingAck := TRUE;
                          }
                          }
                }
            };
                    p6: serverViewNum[self] := view;
                    }
             }
           }
    
}
*)
\* BEGIN TRANSLATION
\* Label vs of process vs at line 66 col 19 changed to vs_
VARIABLES timeOut, pings, view, primary, backup, pendingAck, serverViewNum, 
          pc

vars == << timeOut, pings, view, primary, backup, pendingAck, serverViewNum, 
           pc >>

ProcSet == {0} \cup (Procs)

Init == (* Global variables *)
        /\ timeOut = [i \in Procs |-> 1]
        /\ pings = [i \in Procs |-> 0]
        /\ view = 0
        /\ primary = 0
        /\ backup = 0
        /\ pendingAck = FALSE
        /\ serverViewNum = [i \in Procs |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "vs_"
                                        [] self \in Procs -> "server"]

vs_ == /\ pc[0] = "vs_"
\*       /\ PrintT("vs_")
       /\ pc' = [pc EXCEPT ![0] = "tick"]
       /\ UNCHANGED << timeOut, pings, view, primary, backup, pendingAck, 
                       serverViewNum >>

tick == /\ pc[0] = "tick"
\*        /\ PrintT("tick")
        /\ IF primary # 0
              THEN /\ IF pendingAck = FALSE
                         THEN /\ IF timeOut[primary] = 1
                                    THEN /\ IF backup # 0
                                               THEN /\ primary' = backup
                                                    /\ backup' = 0
                                                    /\ view' = view + 1
                                                    /\ pendingAck' = TRUE
                                               ELSE /\ TRUE
                                                    /\ UNCHANGED << view, 
                                                                    primary, 
                                                                    backup, 
                                                                    pendingAck >>
                                    ELSE /\ TRUE
                                         /\ UNCHANGED << view, primary, backup, 
                                                         pendingAck >>
                         ELSE /\ TRUE
                              /\ UNCHANGED << view, primary, backup, 
                                              pendingAck >>
              ELSE /\ TRUE
                   /\ UNCHANGED << view, primary, backup, pendingAck >>
        /\ IF backup' # 0
              THEN /\ IF timeOut[backup'] = 1
                         THEN /\ pc' = [pc EXCEPT ![0] = "e1"]
                         ELSE /\ pc' = [pc EXCEPT ![0] = "vs_"]
              ELSE /\ pc' = [pc EXCEPT ![0] = "vs_"]
        /\ UNCHANGED << timeOut, pings, serverViewNum >>

e1 == /\ pc[0] = "e1"
\*      /\ PrintT("e1")
      /\ LET i == CHOOSE j \in Procs: \A y \in Procs: pings[j] >= pings[y] IN
           IF timeOut[i] # 1
              THEN /\ backup' = i
                   /\ view' = view + 1
                   /\ pendingAck' = TRUE
              ELSE /\ TRUE
                   /\ UNCHANGED << view, backup, pendingAck >>
      /\ pc' = [pc EXCEPT ![0] = "vs_"]
      /\ UNCHANGED << timeOut, pings, primary, serverViewNum >>

vs == vs_ \/ tick \/ e1
\*vs == vs_

server(self) == /\ pc[self] = "server"
\*                /\ PrintT(self)
\*                /\ PrintT("server")
                /\ \/ /\ timeOut' = [timeOut EXCEPT ![self] = 1]
                      /\ pc' = [pc EXCEPT ![self] = "server"]
                   \/ /\ pc' = [pc EXCEPT ![self] = "p1"]
                      /\ UNCHANGED timeOut
                /\ UNCHANGED << pings, view, primary, backup, pendingAck, 
                                serverViewNum >>

p1(self) == /\ pc[self] = "p1"
\*            /\ PrintT(self)
\*            /\ PrintT("p1")
            /\ timeOut' = [timeOut EXCEPT ![self] = 0]
            /\ pings' = [pings EXCEPT ![self] = pings[self] + 1]
            /\ IF serverViewNum[self] = 0
                  THEN /\ IF self = primary
                             THEN /\ primary' = backup
                                  /\ backup' = 0
                                  /\ view' = view + 1
                                  /\ pendingAck' = TRUE
                             ELSE /\ IF self = backup
                                        THEN /\ backup' = 0
                                        ELSE /\ TRUE
                                             /\ UNCHANGED backup
                                  /\ UNCHANGED << view, primary, pendingAck >>
                  ELSE /\ TRUE
                       /\ UNCHANGED << view, primary, backup, pendingAck >>
            /\ IF pendingAck' = TRUE
                  THEN /\ IF self = primary'
                             THEN /\ IF view' = serverViewNum[self]
                                        THEN /\ pc' = [pc EXCEPT ![self] = "p2"]
                                        ELSE /\ pc' = [pc EXCEPT ![self] = "p6"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "p6"]
                  ELSE /\ IF primary' = 0
                             THEN /\ pc' = [pc EXCEPT ![self] = "p4"]
                             ELSE /\ IF backup' = 0
                                        THEN /\ pc' = [pc EXCEPT ![self] = "p5"]
                                        ELSE /\ pc' = [pc EXCEPT ![self] = "p6"]
            /\ UNCHANGED serverViewNum

p2(self) == /\ pc[self] = "p2"
\*            /\ PrintT(self)
\*            /\ PrintT("p2")
            /\ pendingAck' = FALSE
            /\ pc' = [pc EXCEPT ![self] = "p3"]
            /\ UNCHANGED << timeOut, pings, view, primary, backup, 
                            serverViewNum >>

p3(self) == /\ pc[self] = "p3"
\*            /\ PrintT(self)
\*            /\ PrintT("p3")
            /\ LET i == CHOOSE j \in Procs: \A y \in Procs: pings[j] >= pings[y] IN
                 IF timeOut[i] # 1
                    THEN /\ backup' = i
                         /\ view' = view + 1
                         /\ pendingAck' = TRUE
                    ELSE /\ TRUE
                         /\ UNCHANGED << view, backup, pendingAck >>
            /\ pc' = [pc EXCEPT ![self] = "p6"]
            /\ UNCHANGED << timeOut, pings, primary, serverViewNum >>

p4(self) == /\ pc[self] = "p4"
\*            /\ PrintT(self)
\*            /\ PrintT("p4")
\*            /\ PrintT(view)
\*            /\ PrintT(serverViewNum)
            /\ LET 
                   i == CHOOSE j \in Procs: \A y \in Procs: pings[j] >= pings[y] 
                 IN IF timeOut[i] # 1
                    THEN /\ primary' = i
                         /\ view' = view + 1
                         /\ pendingAck' = TRUE
                    ELSE /\ TRUE
                         /\ UNCHANGED << view, primary, pendingAck >>
            /\ pc' = [pc EXCEPT ![self] = "p6"]
            /\ UNCHANGED << timeOut, pings, backup, serverViewNum >>

p5(self) == /\ pc[self] = "p5"  
\*            /\ PrintT(self)
\*            /\ PrintT("p5")
            /\ LET i == CHOOSE j \in Procs: \A y \in Procs: pings[j] >= pings[y] IN 
                 IF timeOut[i] # 1
                    THEN /\ backup' = i
                         /\ view' = view + 1
                         /\ pendingAck' = TRUE
                    ELSE /\ TRUE
                         /\ UNCHANGED << view, backup, pendingAck >>
            /\ pc' = [pc EXCEPT ![self] = "p6"]
            /\ UNCHANGED << timeOut, pings, primary, serverViewNum >>

p6(self) == /\ pc[self] = "p6"
\*            /\ PrintT(self)
\*            /\ PrintT("p6")
            /\ serverViewNum' = [serverViewNum EXCEPT ![self] = view]
            /\ pc' = [pc EXCEPT ![self] = "server"]
            /\ UNCHANGED << timeOut, pings, view, primary, backup, pendingAck >>

p(self) == server(self) \/ p1(self) \/ p2(self) \/ p3(self) \/ p4(self)
              \/ p5(self) \/ p6(self)

Next == vs
           \/ (\E self \in Procs: p(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(vs)
        /\ \A self \in Procs : WF_vars(p(self))

\* END TRANSLATION



INVARIANT == \A i \in Procs: serverViewNum[i] = view \/ serverViewNum[i] + 1 = view
INVARIANT1 == primary = 0 => backup = 0
=============================================================================
\* Modification History
\* Last modified Tue May 10 17:48:18 MDT 2016 by jiten
\* Created Sat May 07 11:02:10 MDT 2016 by jiten
