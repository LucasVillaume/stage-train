----------------------------- MODULE model2 -----------------------------


EXTENDS Integers, TLC, Sequences\*, scenario_m2 (*
VARIABLE gamma, reg, sigma, feux, meta, rule 


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
            W |-> {}
       ]
    /\ sigma = switch
    /\ feux = [traffic_lights EXCEPT ![3,"L"] = "R",
                                     ![3,"R"] = "R",
                                     ![4,"L"] = "R",
                                     ![4,"R"] = "R"]
    /\ meta = [
            msg   |-> << <<>>, <<>> >>,
            garde |-> [state |-> "none", requests |-> <<>>]
       ]
    /\ rule = "" \* Mesure de débug, pas présent dans le modèle

\* *)
\*Init == Init_S4
\*Suiv(pos, dir, S) == Suiv_S4(pos, dir, S)


\* Utilitaire

Min(S) == CHOOSE x \in S : \A y \in S : x =< y

Max(S) == CHOOSE x \in S : \A y \in S : x >= y

IsInSeq(elem, seq) == \E i \in DOMAIN seq : seq[i] = elem

IsAttTurnInSeq(S) ==
    \E x \in DOMAIN S[2] : 
        S[2][x][1] = "att" \/ S[2][x][1] = "auth" \* True si le tableau comporte une chaîne "att" ou "auth"

NextAttTurn(id, evs) == \*evs : séquence d'events pour un train / evCourante : numéro de l'event courant
    LET 
        res == SelectSeq(evs,IsAttTurnInSeq)
    IN
        IF Len(res) /= 0 THEN res[1][1] \*Il existe un prochain attendre
        ELSE evs[Len(evs)][1] \*Il n'existe pas de prochain attendre (aller à la fin)

IsWaiting(W, block, tvalue) == \E seq \in W : seq[3] = block /\ seq[4] = tvalue

getWaiting(W, block, tvalue) == CHOOSE seq \in W : seq[3] = block /\ seq[4] = tvalue        
        
RequestUpdate(req,F) == [ f \in DOMAIN F |-> IF f[1] = req[1] THEN req[2] ELSE F[f] ]

FindLock(W,E) ==
    [x \in 1..Len(gamma) |->
        IF \E seq \in W : seq[1] = x THEN \* Attend
            gamma[x].pos
        ELSE IF Len(E[x]) = 0 THEN \* Arrivé
            gamma[x].pos
        ELSE \* se déplace
            NextAttTurn(x,E[x])
    ]        

        
UpdateS(S,W,E) == \*S pour Signals
    LET
        locked == FindLock(W,E)
        positions == [ x \in 1..Len(gamma) |-> gamma[x].pos ]
        sigSuiv == [ sig \in DOMAIN S |-> Suiv(sig[1],sig[2],sigma) ] \*reg.S à changer en sigma plus tard
    IN
        [ sig \in DOMAIN S |-> 
            IF IsInSeq(sig[1],locked) THEN \* cas lock
                S[sig]
            ELSE
                IF sigSuiv[sig[1],sig[2]] = -1 THEN \* pas de suivant
                    "R"
                ELSE IF IsInSeq(sigSuiv[sig[1],sig[2]], positions) THEN \* suivant occupé
                    "R"
                ELSE \*suivant non occupé
                    "V"
        ]

\* règles
        \* Train
        
Start(T) == 
    LET
        event == Head(reg.E[T.id])
    IN
        /\ Len(T.prog) > 0
        /\ meta.garde.state = "none"
        /\ T.prog[1][1] = "StartUntil"
        /\ T.prog[1][2] /= T.dir
        /\ gamma' = [gamma EXCEPT ![T.id].dir = T.prog[1][2]]
        /\ rule ' = "start"
        /\ UNCHANGED reg
        /\ UNCHANGED sigma
        /\ UNCHANGED feux
        /\ meta' = [meta EXCEPT !.msg[1] = Append(meta.msg[1],<<T.id,T.pos>>)]  

Stop (T) ==
    LET
        event == Head(reg.E[T.id])
    IN
        /\ Len(T.prog) = 0
        /\ meta.garde.state = "none"
        /\ T.dir /= "*"
        /\ gamma' = [gamma EXCEPT ![T.id].dir = "*"]
        /\ rule' = "stop"
        /\ UNCHANGED reg
        /\ UNCHANGED sigma
        /\ UNCHANGED feux
        /\ meta' = [meta EXCEPT !.msg[1] = Append(meta.msg[1],<<T.id,T.pos>>)]


Until(T) == 
    LET
        id == T.id
        order == Head(T.prog)
        nextC == Suiv(T.pos,T.dir,sigma)
        event == Head(reg.E[id])
    IN
        /\ Len(T.prog) > 0
        /\ meta.garde.state = "none"
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
        /\ UNCHANGED sigma
        /\ UNCHANGED feux
        /\ meta' = [meta EXCEPT !.garde.state = "update", \*"focus",
                                !.msg[1] = Append(meta.msg[1],<<id,nextC>>)]


Until_cons(T) == 
    LET
        id == T.id
        order == Head(T.prog)
        nextC == Suiv(T.pos,T.dir, sigma)
    IN
        /\ Len(T.prog) > 0
        /\ meta.garde.state = "none"
        /\ order[2] = T.dir
        /\ feux[T.pos,T.dir] = "V"
        /\ order[1] = "StartUntil"
        /\ nextC /= -1
        /\ Len(Tail(order[3])) = 0
        /\ gamma' = [gamma EXCEPT 
                            ![T.id].pos = nextC,
                            ![T.id].prog = Tail(T.prog)]
        /\ UNCHANGED feux
        /\ UNCHANGED sigma
        /\ meta' = [meta EXCEPT !.garde.state = "update"] \*"focus"]
        /\ rule' = "until_cons"
        /\ UNCHANGED reg


        \* Regulateur

StartEvent == \*Simuler une approche grands pas
    LET
        id == Head(meta.msg[1])[1]
        pos == Head(meta.msg[1])[2]
    IN
        /\ meta.garde.state = "none"
        /\ Len(meta.msg[1]) /= 0
        /\ UNCHANGED gamma
        /\ UNCHANGED reg
        /\ UNCHANGED sigma
        /\ UNCHANGED feux
        /\ meta' = [meta EXCEPT !.garde.state = "event"]
        /\ rule' = "StartEvent"


Turn == 
    LET
        id == Head(meta.msg[1])[1]
        event == Head(reg.E[id])
        order == Head(event[2])
        numAig == order[2]
    IN
        /\ meta.garde.state = "event"
        /\ Len(meta.msg[1]) /= 0
        /\ Len(event[2]) > 0
        /\ order[1] = "turn"
        /\ numAig <= Len(sigma)
        /\ numAig >= 0
        /\ UNCHANGED gamma
        /\ rule' = "turn" 
        /\ reg' = [reg EXCEPT !.E[id][1][2] = Tail(event[2])]
        /\ sigma' = [sigma EXCEPT ![numAig] = order[3]]
        /\ UNCHANGED feux
        /\ UNCHANGED meta \*' = [meta EXCEPT !.nextG = "update"]

Att_bf == 
    LET
        id == Head(meta.msg[1])[1]
        event == Head(reg.E[id])
        pos == event[1]
        order == Head(event[2])
        jet == order[2]
        val == order[3]
    IN 
        /\ meta.garde.state = "event"
        /\ Len(meta.msg[1]) /= 0
        /\ Len(event[2]) > 0
        /\ order[1] = "att"
        /\ reg.J[jet] /= val
        /\ UNCHANGED gamma
        /\ rule' = "att_bf"
        /\ reg' = [reg EXCEPT !.W = reg.W \union {<<id,pos,jet,val>>},
                              !.E[id][1][2] = Tail(event[2])]
        /\ UNCHANGED sigma
        /\ UNCHANGED feux
        /\ UNCHANGED meta
        
        
Att_af == 
    LET
        id == Head(meta.msg[1])[1]
        event == Head(reg.E[id])
        pos == event[1]
        order == Head(event[2])
        jet == order[2]
        val == order[3]
        subseqEv == SubSeq(reg.E[id],2,Len(reg.E[id]))
        target == NextAttTurn(id,subseqEv)
    IN
        /\ meta.garde.state = "event"
        /\ Len(meta.msg[1]) /= 0
        /\ Len(event[2]) > 0
        /\ order[1] = "att"
        /\ reg.J[jet] = val
        /\ UNCHANGED gamma
        /\ rule' = "att_af"
        /\ reg' = [reg EXCEPT !.E[id][1][2] = Tail(event[2])]
        /\ UNCHANGED sigma
        /\ UNCHANGED feux
        /\ meta' = [meta EXCEPT !.garde.requests = meta.garde.requests \o << <<target,"R">>, <<pos,"V">> >>]

Incr_bf ==
    LET
        id == Head(meta.msg[1])[1]
        event == Head(reg.E[id])
        order == Head(event[2])
        jet == order[2]
        val == reg.J[jet]
    IN
        /\ meta.garde.state = "event"
        /\ Len(meta.msg[1]) /= 0
        /\ Len(event[2]) > 0
        /\ order[1] = "incr"
        /\ ~IsWaiting(reg.W,jet,val+1) \*Personne n'attend encore
        /\ UNCHANGED gamma
        /\ rule' = "incr_bf"
        /\ reg' = [reg EXCEPT !.J[jet] = reg.J[jet]+1,
                              !.E[id][1][2] = Tail(event[2])]
        /\ UNCHANGED sigma
        /\ UNCHANGED feux
        /\ UNCHANGED meta


Incr_af ==
    LET
        id == Head(meta.msg[1])[1]
        event == Head(reg.E[id])
        order == Head(event[2])
        jet == order[2]
        val == reg.J[jet]
        
        info_wait == getWaiting(reg.W,jet,val+1)
        id_wait == info_wait[1] \*possiblement inutile
        subseqEv == SubSeq(reg.E[id_wait],1,Len(reg.E[id_wait]))
        target == NextAttTurn(id_wait,subseqEv)
        pos == info_wait[2]
    IN
        /\ meta.garde.state = "event"
        /\ Len(meta.msg[1]) /= 0
        /\ Len(event[2]) > 0
        /\ order[1] = "incr"
        /\ IsWaiting(reg.W,jet,val+1)
        /\ UNCHANGED gamma
        /\ rule' = "incr_af "
        /\ reg' = [reg EXCEPT !.J[jet] = reg.J[jet]+1,
                              !.W = {seq \in reg.W : seq /= info_wait}, \*test
                              !.E[id][1][2] = Tail(event[2])]
        /\ UNCHANGED sigma
        /\ UNCHANGED feux
        /\ meta' = [meta EXCEPT !.garde.requests = meta.garde.requests \o << <<target,"R">>, <<pos,"V">> >>] \*si tous marche bien, inutile plus tard
               \*                 !.nextG = "update"]


Auth ==
    LET
        id == Head(meta.msg[1])[1]
        event == Head(reg.E[id])
        pos == event[1]
        order == Head(event[2])
        subseqEv == SubSeq(reg.E[id],2,Len(reg.E[id]))
        target == NextAttTurn(id,subseqEv)
    IN
        /\ meta.garde.state = "event"
        /\ Len(meta.msg[1]) /= 0
        /\ Len(event[2]) > 0
        /\ order[1] = "auth"
        /\ UNCHANGED gamma
        /\ rule' = "auth"
        /\ reg' = [reg EXCEPT !.E[id][1][2] = Tail(event[2])]
        /\ UNCHANGED sigma
        /\ UNCHANGED feux
        /\ meta' = [meta EXCEPT !.garde.requests = meta.garde.requests \o << <<target,"R">>, <<pos,"V">> >>] \*si tous marche bien, inutile plus tard
               \*                 !.nextG = "update"]



EndEvent ==
    LET
        id == Head(meta.msg[1])[1]
        event == Head(reg.E[id])
    IN
        /\ meta.garde.state = "event"
        /\ Len(meta.msg[1]) /= 0
        /\ Len(event[2]) = 0
        /\ UNCHANGED gamma
        /\ rule' = "EndEvent"
        /\ reg' = [reg EXCEPT !.E[id] = Tail(reg.E[id])]
        /\ UNCHANGED sigma
        /\ UNCHANGED feux
        /\ meta' = [meta EXCEPT !.garde.state = "update", \*meta.nextG,
                                \*!.nextG = "none",
                                !.msg[1] = Tail(meta.msg[1])]


        \* Feu

ReqUpdate ==
    LET
        req == Head(meta.garde.requests)
    IN
        /\ meta.garde.state = "update"
        /\ Len(meta.garde.requests) > 0
        /\ UNCHANGED gamma
        /\ UNCHANGED reg
        /\ UNCHANGED sigma
        /\ rule' = "ReqUpdate"
        /\ feux' = RequestUpdate(req,feux)
        /\ meta' = [meta EXCEPT !.garde.requests = Tail(meta.garde.requests)]


UpdateTL ==
    /\ meta.garde.state = "update"
    /\ Len(meta.garde.requests) = 0
    /\ UNCHANGED gamma
    /\ UNCHANGED reg
    /\ UNCHANGED sigma
    /\ rule' = "UpdateTL"
    /\ feux' = UpdateS(feux,reg.W,reg.E)
    /\ meta' = [meta EXCEPT !.garde.state = "none"]
        
        


IDLE ==
    \A t \in 1..Len(gamma):
        /\ Len(gamma[t].prog) = 0
        /\ gamma[t].dir = "*"
    /\ Len(meta.msg[1]) = 0
    /\ UNCHANGED gamma
    /\ rule' = "IDLE"
    /\ UNCHANGED feux
    /\ UNCHANGED meta
    /\ UNCHANGED reg
    /\ UNCHANGED sigma
    

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
        \*\/ ReqFocus
        \*\/ FocusTL
        \/ ReqUpdate
        \/ UpdateTL
        \/ IDLE
        

Spec == Init /\ [][Next]_<<gamma,reg,sigma,feux,meta,rule>> /\ WF_<<gamma,reg,sigma,feux,meta,rule>>(Next)
\* WF_ : Weak Fairness, "si une règle peut être appliquée, je l'applique"

set == {<<1,4,5,7>>,<<2,6,5,8>>}

Eval ==  \E seq \in set : seq[1] = 2 \*SelectSeq(<< <<8,<<<<"">>, <<"">>, <<" ">>>>>>, <<2,<<<<"att">>>>>> >>, IsAttTurnInSeq)[1][1] \*"Hello" \o " World !"

=============================================================================
\* Modification History
\* Last modified Thu Jun 19 09:40:14 CEST 2025 by lucas
\* Created Fri May 09 16:46:37 CEST 2025 by lucas
