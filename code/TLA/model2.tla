----------------------------- MODULE model2 -----------------------------


EXTENDS Integers, TLC, Sequences, scenario_m2 (*
VARIABLE gamma, reg, rule, msg, feux, garde


nbCanton == 4 \* Nombre de canton du circuit
maxVal == 3 \* Valeur max que peut prendre un jeton
nbTrain == 2

\*Trains
train1 == [
    id |-> 1,
    pos |-> 1,
    dir |-> "*",
    prog |-> << <<"StartUntil", "R", <<2,3>> >> >>
]

train2 == [
    id |-> 2,
    pos |-> 4,
    dir |-> "*",
    prog |-> << <<"StartUntil", "L", <<2,1>> >> >>
]

\* Régulateur
events == <<
        << <<1,<<>>>>, <<2,<<>>>>, <<3,<<<<"turn",1,"v">>,<<"incr",2>>>>>> >>,
        << <<4,<<<<"att",2,1>>>>>>, <<2,<<>>>>, <<1,<<>>>> >>
     >>

token == [x \in 1..nbCanton |-> 0]

wait == [x \in (1..nbCanton) \X (0..maxVal) |-> -1] 

switch == <<"d">>

historique == [x \in (1..nbTrain) |-> -1]

traffic_lights == [x \in (1..nbCanton) \X {"L","R"} |-> "V"]

Suiv(pos, dir, S) == IF pos = 1 /\ dir = "R"               THEN 2
                ELSE IF pos = 2 /\ dir = "R" /\ S[1] = "d" THEN 3
                ELSE IF pos = 2 /\ dir = "R" /\ S[1] = "v" THEN 4
                ELSE IF pos = 2 /\ dir = "L"               THEN 1
                ELSE IF pos = 3 /\ dir = "L" /\ S[1] = "d" THEN 2
                ELSE IF pos = 4 /\ dir = "L" /\ S[1] = "v" THEN 2
                ELSE -1
                

Init == 
    /\ gamma = <<train1,train2>>
    /\ reg = [
            E |-> events,
            J |-> token,
            S |-> switch,
            W |-> wait,
            F |-> "none", \* modification des feux dans l'event
            H |-> historique
       ]
    /\ feux = [traffic_lights EXCEPT ![3,"L"] = "R",
                                     ![3,"R"] = "R",
                                     ![4,"L"] = "R",
                                     ![4,"R"] = "R"]
    /\ garde = [
            state |-> "none",
            requests |-> <<>>
       ]
    /\ rule = "" \* Mesure de débug, pas présent dans le modèle
    /\ msg = << <<>>, <<>> >>

\* *)
Init == Init_S4
Suiv(pos, dir, S) == Suiv_S4(pos, dir, S)


\* Utilitaire

Min(S) == CHOOSE x \in S : \A y \in S : x =< y

IsAttTurnInSeq(S) == 
    \E x \in DOMAIN S[2] : 
        S[2][x][1] = "att" \/ S[2][x][1] = "turn" \* True si le tableau comporte une chaîne "att" ou "turn"

NextAttTurn(id, evs) == \*evs : séquence d'events pour un train / evCourante : numéro de l'event courant
    LET 
        res == SelectSeq(evs,IsAttTurnInSeq)
    IN
        IF Len(res) /= 0 THEN res[1][1] \*Il existe un prochain attendre
        ELSE evs[Len(evs)][1] \*Il n'existe pas de prochain attendre (aller à la fin)

Failsafe(f) == IF Suiv(f[1],f[2],reg.S) = -1 THEN "R" ELSE feux[f[1],f[2]]

UpdateF(F) == [f \in DOMAIN F |-> Failsafe(f)]

RequestFocus(req,F) == \* uniquement pour règles Until
    LET
        pos == req[1]
        prec == req[2]
        dir == req[3]
        dir_op == IF dir = "R" THEN "L" ELSE "R"
        next == Suiv(pos,dir,reg.S)
    IN
        [f \in DOMAIN F |-> IF f = <<prec,dir>> \/ f = <<next,dir_op>> THEN "R" ELSE F[f] ]

RequestUpdate(req,F) == [f \in DOMAIN F |-> IF f[1] = req[1] THEN req[2] ELSE F[f] ]

\* règles
        \* Train
        
Start(T) == 
    LET
        event == Head(reg.E[T.id])
    IN
        /\ Len(T.prog) > 0
        /\ garde.state = "none"
        /\ T.prog[1][1] = "StartUntil"
        /\ T.prog[1][2] /= T.dir
        /\ gamma' = [gamma EXCEPT ![T.id].dir = T.prog[1][2]]
        /\ rule ' = "start"
        /\ UNCHANGED reg
        /\ UNCHANGED feux
        /\ UNCHANGED garde
        /\ msg' = [msg EXCEPT ![1] = Append(msg[1],<<T.id,T.pos>>)]

Stop (T) ==
    LET
        event == Head(reg.E[T.id])
    IN
        /\ Len(T.prog) = 0
        /\ garde.state = "none"
        /\ T.dir /= "*"
        /\ gamma' = [gamma EXCEPT ![T.id].dir = "*"]
        /\ rule' = "stop"
        /\ UNCHANGED reg
        /\ UNCHANGED feux
        /\ UNCHANGED garde
        /\ msg' = [msg EXCEPT ![1] = Append(msg[1],<<T.id,T.pos>>)]


Until(T) == 
    LET
        id == T.id
        order == Head(T.prog)
        nextC == Suiv(T.pos,T.dir,reg.S)
        event == Head(reg.E[id])
    IN
        /\ Len(T.prog) > 0
        /\ garde.state = "none"
        /\ order[2] = T.dir 
        /\ feux[T.pos,T.dir] = "V"
        /\ order[1] = "StartUntil"
        /\ nextC /= -1
        /\ Len(Tail(order[3])) /= 0
        /\ gamma' = [gamma EXCEPT 
                            ![id].pos = nextC,
                            ![id].prog[1][3] = Tail(order[3])]
        /\ rule' = "until"
        /\ UNCHANGED reg
        /\ UNCHANGED feux
        /\ garde' = [garde EXCEPT !.state = "focus",
                                  !.requests = Append(garde.requests, <<nextC, T.pos, T.dir>>)]
        /\ IF Len(reg.E[id]) > 0 THEN
                msg' = [msg EXCEPT ![1] = Append(msg[1],<<id,nextC>>)]
           ELSE
            UNCHANGED msg



Until_cons(T) == 
    LET
        id == T.id
        order == Head(T.prog)
        nextC == Suiv(T.pos,T.dir, reg.S)
    IN
        /\ Len(T.prog) > 0
        /\ garde.state = "none"
        /\ order[2] = T.dir
        /\ feux[T.pos,T.dir] = "V"
        /\ order[1] = "StartUntil"
        /\ nextC /= -1
        /\ Len(Tail(order[3])) = 0
        /\ gamma' = [gamma EXCEPT 
                            ![T.id].pos = nextC,
                            ![T.id].prog = Tail(T.prog)]
        /\ UNCHANGED feux
        /\ garde' = [garde EXCEPT !.state = "focus",
                                  !.requests = Append(garde.requests, <<nextC, T.pos, T.dir>>)]
        /\ rule' = "until_cons"
        /\ UNCHANGED <<reg,msg>>


        \* Regulateur

StartEvent == \*Simuler une approche grands pas
    LET
        id == Head(msg[1])[1]
        pos == Head(msg[1])[2]
    IN
        /\ garde.state = "none"
        /\ Len(msg[1]) /= 0
        /\ UNCHANGED gamma
        /\ reg' = [reg EXCEPT !.H[id] = pos] \* actualise la position du train dans l'historique
        /\ UNCHANGED feux
        /\ garde' = [garde EXCEPT !.state = "event"]
        /\ rule' = "StartEvent"
        /\ UNCHANGED msg


Turn == 
    LET
        id == Head(msg[1])[1]
        event == Head(reg.E[id])
        order == Head(event[2])
        numAig == order[2]
    IN
        /\ garde.state = "event"
        /\ Len(msg[1]) /= 0
        /\ Len(event[2]) > 0
        /\ order[1] = "turn"
        /\ numAig <= Len(reg.S)
        /\ numAig >= 0
        /\ UNCHANGED gamma
        /\ rule' = "turn" 
        /\ reg' = [reg EXCEPT !.S[numAig] = order[3],
                              !.F = "update",
                              !.E[id][1][2] = Tail(event[2])]
        /\ UNCHANGED feux
        /\ UNCHANGED garde
        /\ UNCHANGED msg

Att_bf == 
    LET
        id == Head(msg[1])[1]
        event == Head(reg.E[id])
        order == Head(event[2])
        jet == order[2]
        val == order[3]
    IN 
        /\ garde.state = "event"
        /\ Len(msg[1]) /= 0
        /\ Len(event[2]) > 0
        /\ order[1] = "att"
        /\ reg.J[jet] /= val
        /\ UNCHANGED gamma
        /\ rule' = "att_bf"
        /\ reg' = [reg EXCEPT !.W[jet,val] = id,
                              !.E[id][1][2] = Tail(event[2])]
        /\ UNCHANGED feux
        /\ UNCHANGED garde
        /\ UNCHANGED msg

Att_af == 
    LET
        id == Head(msg[1])[1]
        event == Head(reg.E[id])
        order == Head(event[2])
        jet == order[2]
        val == order[3]
        subseqEv == SubSeq(reg.E[id],2,Len(reg.E[id]))
        target == NextAttTurn(id,subseqEv)
        pos == reg.H[id]
    IN
        /\ garde.state = "event"
        /\ Len(msg[1]) /= 0
        /\ Len(event[2]) > 0
        /\ order[1] = "att"
        /\ reg.J[jet] = val
        /\ UNCHANGED gamma
        /\ rule' = "att_af" \o ToString(pos) \o ToString(target)
        /\ reg' = [reg EXCEPT !.W[jet,val] = id,
                              !.F = "update",
                              !.E[id][1][2] = Tail(event[2])]
        /\ UNCHANGED feux
        /\ garde' = [garde EXCEPT !.requests = garde.requests \o << <<target,"R">>, <<pos,"V">> >>]
        /\ UNCHANGED msg

Incr_bf ==
    LET
        id == Head(msg[1])[1]
        event == Head(reg.E[id])
        order == Head(event[2])
        jet == order[2]
        val == reg.J[jet]
        id_wait == reg.W[jet,val+1]
    IN
        /\ garde.state = "event"
        /\ Len(msg[1]) /= 0
        /\ Len(event[2]) > 0
        /\ order[1] = "incr"
        /\ id_wait = -1
        /\ UNCHANGED gamma
        /\ rule' = "incr_bf"
        /\ reg' = [reg EXCEPT !.J[jet] = reg.J[jet]+1,
                              !.E[id][1][2] = Tail(event[2])]
        /\ UNCHANGED feux
        /\ UNCHANGED garde
        /\ UNCHANGED msg


Incr_af ==
    LET
        id == Head(msg[1])[1]
        event == Head(reg.E[id])
        order == Head(event[2])
        jet == order[2]
        val == reg.J[jet]
        id_wait == reg.W[jet,val+1]
        subseqEv == SubSeq(reg.E[id_wait],1,Len(reg.E[id_wait]))
        target == NextAttTurn(id_wait,subseqEv)
        pos == reg.H[id_wait]
    IN
        /\ garde.state = "event"
        /\ Len(msg[1]) /= 0
        /\ Len(event[2]) > 0
        /\ order[1] = "incr"
        /\ id_wait /= -1
        /\ UNCHANGED gamma
        /\ rule' = "incr_af "
        /\ reg' = [reg EXCEPT !.J[jet] = reg.J[jet]+1,
                              !.F = "update",
                              !.E[id][1][2] = Tail(event[2])]
        /\ UNCHANGED feux
        /\ garde' = [garde EXCEPT !.requests = garde.requests \o << <<target,"R">>, <<pos,"V">> >>]
        /\ UNCHANGED msg


Auth ==
    LET
        id == Head(msg[1])[1]
        event == Head(reg.E[id])
        order == Head(event[2])
        subseqEv == SubSeq(reg.E[id],2,Len(reg.E[id]))
        target == NextAttTurn(id,subseqEv)
        pos == reg.H[id]
    IN
        /\ garde.state = "event"
        /\ Len(msg[1]) /= 0
        /\ Len(event[2]) > 0
        /\ order[1] = "auth"
        /\ UNCHANGED gamma
        /\ rule' = "auth"
        /\ reg' = [reg EXCEPT !.E[id][1][2] = Tail(event[2]),
                              !.F = "update"]
        /\ UNCHANGED feux
        /\ garde' = [garde EXCEPT !.requests = garde.requests \o << <<target,"R">>, <<pos,"V">> >>]
        /\ UNCHANGED msg



EndEvent ==
    LET
        id == Head(msg[1])[1]
        event == Head(reg.E[id])
    IN
        /\ garde.state = "event"
        /\ Len(msg[1]) /= 0
        /\ Len(event[2]) = 0
        /\ UNCHANGED gamma
        /\ rule' = "EndEvent"
        /\ reg' = [reg EXCEPT !.E[id] = Tail(reg.E[id]),
                              !.F = "none"]
        /\ UNCHANGED feux
        /\ garde' = [garde EXCEPT !.state = reg.F]
        /\ msg' = [msg EXCEPT ![1] = Tail(msg[1])]


        \* Feux

ReqFocus ==
    LET
        req == Head(garde.requests)
    IN
        /\ garde.state = "focus"
        /\ Len(garde.requests) > 0
        /\ UNCHANGED gamma
        /\ UNCHANGED reg
        /\ rule' = "ReqFocus"
        /\ feux' = RequestFocus(req,feux)
        /\ garde' = [garde EXCEPT !.state = "none",
                                  !.requests = Tail(garde.requests)]
        /\ UNCHANGED msg


ReqUpdate ==
    LET
        req == Head(garde.requests)
    IN
        /\ garde.state = "update"
        /\ Len(garde.requests) > 0
        /\ UNCHANGED gamma
        /\ UNCHANGED reg
        /\ rule' = "ReqUpdate"
        /\ feux' = RequestUpdate(req,feux)
        /\ garde' = [garde EXCEPT !.requests = Tail(garde.requests)]
        /\ UNCHANGED msg


UpdateTL ==
    /\ garde.state = "update"
    /\ Len(garde.requests) = 0
    /\ UNCHANGED gamma
    /\ UNCHANGED reg
    /\ rule' = "UpdateTL"
    /\ feux' = UpdateF(feux)
    /\ garde' = [garde EXCEPT !.state = "none"]
    /\ UNCHANGED msg
        
        


IDLE ==
    \A t \in 1..Len(gamma):
        /\ Len(gamma[t].prog) = 0
        /\ gamma[t].dir = "*"
    /\ Len(msg[1]) = 0
    /\ UNCHANGED gamma
    /\ rule' = "IDLE"
    /\ UNCHANGED feux
    /\ UNCHANGED garde
    /\ UNCHANGED reg
    /\ UNCHANGED msg

\* Propriétés

Liveness == 
    /\  <>[] /\ gamma[1].pos = 7
             /\ gamma[1].dir = "*"
    /\  <>[] /\ gamma[2].pos = 3
             /\ gamma[2].dir = "*"

Safety == [] (gamma[1].pos /= gamma[2].pos)

\* Spec

Next == 
    \E i \in 1..Len(gamma) :
        \/ Start(gamma[i])
        \/ Until(gamma[i])
        \/ Until_cons(gamma[i])
        \/ Stop(gamma[i])
        \/ StartEvent
        \/ Turn
        \/ Incr_bf
        \/ Incr_af
        \/ Att_bf
        \/ Att_af
        \/ Auth
        \/ EndEvent
        \/ ReqFocus
        \/ ReqUpdate
        \/ UpdateTL
        \/ IDLE
        

Spec == Init /\ [][Next]_<<gamma,reg,rule,msg,feux,garde>> /\ WF_<<gamma,reg,rule,msg,feux,garde>>(Next)
\* WF_ : Weak Fairness, "si une règle peut être appliquée, je l'applique"


Eval ==  SelectSeq(<< <<8,<<<<"">>, <<"">>, <<" ">>>>>>, <<2,<<<<"">>>>>> >>, IsAttTurnInSeq)[1][1] \*"Hello" \o " World !"

=============================================================================
\* Modification History
\* Last modified Fri Jun 13 11:56:59 CEST 2025 by lucas
\* Created Fri May 09 16:46:37 CEST 2025 by lucas
