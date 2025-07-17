----------------------------- MODULE model3 -----------------------------


EXTENDS Integers, TLC, Sequences\*, scenario_m3 (*
VARIABLE gamma, reg, sigma, feux, meta, rule 


nbCanton == 4 \* Nombre de canton du circuit
maxVal == 3 \* Valeur max que peut prendre un jeton
nbTrain == 2

\*Trains
train1 == [
    id |-> 1,
    pos |-> 1,
    dir |-> "*",
    prog |-> << <<"Start", "R">>, <<"Until", <<2,3>> >> >>,
    tpos |-> 1
]

train2 == [
    id |-> 2,
    pos |-> 4,
    dir |-> "*",
    prog |-> << <<"Start", "L" >>, <<"Until", <<2,1>> >> >>,
    tpos |-> 4
]

\* Régulateur
old_events == <<
        << <<1,<<<<"incr",1>>>>>>, <<2,<<>>>>, <<3,<<<<"turn",1,"v">>,<<"incr",2>>>>>> >>,
        << <<4,<<<<"incr",4>>,<<"att",2,1>>>>>>, <<2,<<>>>>, <<1,<<>>>> >>
     >>

events == [ [x \in (1..nbCanton) \X {"L","R"} |-> << >>] EXCEPT ![1,"L"] = << <<>> >>,
                                                                ![1,"R"] = << <<<<"incr",1>>>>, <<>> >>,
                                                                ![2,"L"] = << <<>>, <<>> >>,
                                                                ![2,"R"] = << <<>>, <<>> >>,
                                                                ![3,"R"] = << <<<<"turn",1,"v">>,<<"incr",2>>>> >>,
                                                                ![3,"L"] = << <<>> >>,
                                                                ![4,"L"] = << <<<<"incr",4>>,<<"att",2,1>>>> >> ]


token == [x \in 1..nbCanton |-> 0]

wait == [x \in (1..nbCanton) \X (0..maxVal) |-> -1]

switch == <<"d">>

historique == [x \in (1..nbTrain) |-> -1]

traffic_lights == [x \in (1..nbCanton) \X {"L","R"} |-> "V"]


checkpoint == <<<<-1>>,<<4,-1>>>> \*chekcpoint[1] = train1


Suiv(pos, dir, S) == IF pos = 1 /\ dir = "R"               THEN 2
                ELSE IF pos = 2 /\ dir = "L"               THEN 1
                ELSE IF pos = 2 /\ dir = "R" /\ S[1] = "d" THEN 3
                ELSE IF pos = 2 /\ dir = "R" /\ S[1] = "v" THEN 4
                ELSE IF pos = 3 /\ dir = "L" /\ S[1] = "d" THEN 2
                ELSE IF pos = 4 /\ dir = "L" /\ S[1] = "v" THEN 2
                ELSE -1


SuivR(pos, dir, S) == IF pos = 1 /\ dir = "R"               THEN 2
                 ELSE IF pos = 2 /\ dir = "R"               THEN 5 \* switch
                 ELSE IF pos = 2 /\ dir = "L"               THEN 1
                 ELSE IF pos = 3 /\ dir = "L" /\ S[1] = "d" THEN 5
                 ELSE IF pos = 4 /\ dir = "L" /\ S[1] = "v" THEN 5
                 ELSE IF pos = 5 /\ dir = "L" /\ S[1] = "d" THEN 2
                 ELSE IF pos = 5 /\ dir = "L" /\ S[1] = "v" THEN 2
                 ELSE IF pos = 5 /\ dir = "R" /\ S[1] = "d" THEN 3
                 ELSE IF pos = 5 /\ dir = "R" /\ S[1] = "v" THEN 4
                 ELSE -1
                


Init == 
    /\ gamma = <<train1,train2>>
    /\ reg = [
            E  |-> events,
            J  |-> token,
            W  |-> {<<1,1,1,1>>,<<2,4,4,1>>},
            H  |-> << <<1,"R">>, <<4,"L">> >>,
            CP |-> checkpoint
       ]
    /\ sigma = switch
    /\ feux = [traffic_lights EXCEPT ![1,"L"] = "R",
                                     ![1,"R"] = "R",
                                     ![4,"L"] = "R",
                                     ![4,"R"] = "R"]
    /\ meta = [
            msg   |-> << <<>>, <<>> >>,
            garde |-> [state |-> "none", requests |-> <<>>]
       ]
    /\ rule = "" \* Mesure de débug, pas présent dans le modèle

\*)
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
        ELSE -1 \*evs[Len(evs)][1] \*Il n'existe pas de prochain attendre (aller à la fin)

IsWaiting(W, block, tvalue) == \E seq \in W : seq[3] = block /\ seq[4] = tvalue

getWaiting(W, block, tvalue) == CHOOSE seq \in W : seq[3] = block /\ seq[4] = tvalue  

reversedGetWaiting(W, tid) == CHOOSE seq \in W : seq[1] = tid
        
RequestUpdate(req,F) == [ f \in DOMAIN F |-> IF f[1] = req[1] THEN req[2] ELSE F[f] ]

FindLock(W,CP) ==
    LET
        pos(tid) == reversedGetWaiting(W,tid)[2]
    IN
    [x \in 1..Len(gamma) |->
        IF \E seq \in W : seq[1] = x THEN \* Attend
            pos(x)
        ELSE IF Len(CP[x]) < 2 THEN \* Arrivé
            0 
        ELSE \* se déplace
            Head(CP[x])
    ]        

        
UpdateS(S,W,CP) == \*S pour Signals
    LET
        locked == FindLock(W,CP)
        positions == [ x \in 1..Len(gamma) |-> gamma[x].pos ]
        sigSuiv == [ sig \in DOMAIN S |-> Suiv(sig[1],sig[2],sigma) ]
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
        

Stalk(H, sig, capteur) ==
    LET
        getByPos(p) == CHOOSE x \in DOMAIN H : H[x][1] = p
        getBySuiv(c) == CHOOSE x \in DOMAIN H : Suiv(H[x][1], H[x][2], sig) = c[1] /\ H[x][2] /= c[2]
    IN
        IF \E i \in DOMAIN H : H[i][1] = capteur[1] THEN
            IF H[getByPos(capteur[1])][2] /= capteur[2] THEN
                [H EXCEPT ![getByPos(capteur[1])] = <<capteur[1], capteur[2]>>]
            ELSE
                H
        ELSE IF \E i \in DOMAIN H : Suiv(H[i][1], H[i][2], sig) = capteur[1] THEN
            [H EXCEPT ![getBySuiv(capteur)] = <<capteur[1], H[getBySuiv(capteur)][2]>>]
        ELSE
            -1



\* règles
        \* Train
        
Start(T) == 
    LET
        event == Head(reg.E[T.id])
    IN
        /\ Len(T.prog) > 0
        /\ meta.garde.state = "none"
        /\ T.prog[1][1] = "Start"
        /\ T.prog[1][2] /= T.dir
        /\ gamma' = [gamma EXCEPT ![T.id].dir = T.prog[1][2],
                                  ![T.id].prog = Tail(T.prog)]
        /\ rule ' = "start"
        /\ UNCHANGED reg
        /\ UNCHANGED sigma
        /\ UNCHANGED feux
        /\ meta' = [meta EXCEPT !.msg[1] = meta.msg[1] \o << <<T.pos,T.prog[1][2],T.id>> >>]


Stop(T) ==
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
        /\ UNCHANGED meta


Until(T) == 
    LET
        id == T.id
        order == Head(T.prog)
        nextC == SuivR(T.pos,T.dir,sigma)
        event == Head(reg.E[id])
        opDir == IF T.dir = "L" THEN "R" ELSE "L"
    IN
        /\ Len(T.prog) > 0
        /\ meta.garde.state = "none"
        /\ T.dir /= "*" 
        /\ feux[T.pos,T.dir] = "V"
        /\ order[1] = "Until"
        /\ nextC /= -1
        /\ nextC <= nbCanton
        /\ Len(Tail(order[2])) /= 0
        /\ gamma' = [gamma EXCEPT 
                            ![id].pos = nextC,
                            ![T.id].tpos = nextC, \* modèle 3
                            ![id].prog[1][2] = Tail(order[2])]
        /\ rule' = "until"
        /\ UNCHANGED reg
        /\ UNCHANGED sigma
        /\ UNCHANGED feux
        /\ meta' = [meta EXCEPT !.garde.state = "update",
                                !.msg[1] = meta.msg[1] \o << <<nextC,opDir>>,<<nextC,T.dir>> >>]


Until_cons(T) == 
    LET
        id == T.id
        order == Head(T.prog)
        nextC == SuivR(T.pos,T.dir, sigma)
        opDir == IF T.dir = "L" THEN "R" ELSE "L" 
    IN
        /\ Len(T.prog) > 0
        /\ meta.garde.state = "none"
        /\ T.dir /= "*"
        /\ feux[T.pos,T.dir] = "V"
        /\ order[1] = "Until"
        /\ nextC /= -1
        /\ nextC <= nbCanton
        /\ Len(Tail(order[2])) = 0
        /\ gamma' = [gamma EXCEPT 
                            ![T.id].pos = nextC,
                            ![T.id].tpos = nextC, \* modèle 3
                            ![T.id].prog = Tail(T.prog)]
        /\ UNCHANGED feux
        /\ UNCHANGED sigma
        /\ meta' = [meta EXCEPT !.garde.state = "update",
                                !.msg[1] = meta.msg[1] \o << <<nextC,opDir>>,<<nextC,T.dir>> >>]
        /\ rule' = "until_cons"
        /\ UNCHANGED reg


ExitBlock(T) ==
    LET
        id == T.id
        order == Head(T.prog)
        nextC == SuivR(T.tpos,T.dir,sigma)
        event == Head(reg.E[id])
    IN
        /\ Len(T.prog) > 0
        /\ meta.garde.state = "none"
        /\ T.dir /= "*" 
        /\ feux[T.pos,T.dir] = "V"
        /\ order[1] = "Until"
        /\ nextC > nbCanton
        /\ gamma' = [gamma EXCEPT ![id].tpos = nextC]
        /\ rule' = "exitBlock"
        /\ UNCHANGED reg
        /\ UNCHANGED sigma
        /\ UNCHANGED feux
        /\ UNCHANGED meta
        
        
EnterSwitch(T) ==
    LET
        id == T.id
        order == Head(T.prog)
        nextC == SuivR(T.tpos,T.dir,sigma)
        event == Head(reg.E[id])
    IN
        /\ Len(T.prog) > 0
        /\ meta.garde.state = "none"
        /\ T.dir /= "*" 
        /\ order[1] = "Until"
        /\ nextC > nbCanton
        /\ gamma' = [gamma EXCEPT ![id].tpos = nextC]
        /\ rule' = "enterSwitch"
        /\ UNCHANGED reg
        /\ UNCHANGED sigma
        /\ UNCHANGED feux
        /\ UNCHANGED meta
        
        
EnterBlock(T) ==
    LET
        id == T.id
        order == Head(T.prog)
        nextC == SuivR(T.tpos,T.dir,sigma)
        event == Head(reg.E[id])
        opDir == IF T.dir = "L" THEN "R" ELSE "L"
    IN
        /\ Len(T.prog) > 0
        /\ meta.garde.state = "none"
        /\ T.dir /= "*" 
        /\ order[1] = "Until"
        /\ nextC /= -1
        /\ nextC <= nbCanton
        /\ Len(Tail(order[2])) /= 0
        /\ gamma' = [gamma EXCEPT 
                            ![id].pos = nextC,
                            ![T.id].tpos = nextC, \* modèle 3
                            ![id].prog[1][2] = Tail(order[2])]
        /\ rule' = "enterBlock"
        /\ UNCHANGED reg
        /\ UNCHANGED sigma
        /\ UNCHANGED feux
        /\ meta' = [meta EXCEPT !.garde.state = "update",
                                !.msg[1] = meta.msg[1] \o << <<nextC,opDir>>,<<nextC,T.dir>> >>]


EnterBlock_cons(T) == 
    LET
        id == T.id
        order == Head(T.prog)
        nextC == SuivR(T.tpos, T.dir, sigma)
        opDir == IF T.dir = "L" THEN "R" ELSE "L" 
    IN
        /\ Len(T.prog) > 0
        /\ meta.garde.state = "none"
        /\ T.dir /= "*"
        /\ order[1] = "Until"
        /\ nextC /= -1
        /\ nextC <= nbCanton
        /\ Len(Tail(order[2])) = 0
        /\ gamma' = [gamma EXCEPT 
                            ![T.id].pos = nextC,
                            ![T.id].tpos = nextC, \* modèle 3
                            ![T.id].prog = Tail(T.prog)]
        /\ UNCHANGED feux
        /\ UNCHANGED sigma
        /\ meta' = [meta EXCEPT !.garde.state = "update",
                                !.msg[1] = meta.msg[1] \o << <<nextC,opDir>>,<<nextC,T.dir>> >>]
        /\ rule' = "enterBlock_cons"
        /\ UNCHANGED reg


        \* Regulateur
        

StartEvent == \*Simuler une approche grands pas
    /\ meta.garde.state = "none"
    /\ Len(meta.msg[1]) /= 0
    /\ UNCHANGED gamma
    /\ reg' = [reg EXCEPT !.H = Stalk(reg.H,sigma,Head(meta.msg[1]))]
    /\ UNCHANGED sigma
    /\ UNCHANGED feux
    /\ meta' = [meta EXCEPT !.garde.state = "event"]
    /\ rule' = "StartEvent"
    \*/\ PrintT(<<reg.J,meta.msg,feux,gamma>>)


Turn == 
    LET
        i == Head(meta.msg[1]) \*id du capteur <<bid,dir>>
        id == <<i[1],i[2]>>
        event == Head(reg.E[id])
        order == Head(event)
        numAig == order[2]
    IN
        /\ meta.garde.state = "event"
        /\ Len(meta.msg[1]) /= 0
        /\ Len(event) > 0
        /\ order[1] = "turn"
        /\ numAig <= Len(sigma)
        /\ numAig >= 0
        /\ UNCHANGED gamma
        /\ rule' = "turn" 
        /\ reg' = [reg EXCEPT !.E[id][1] = Tail(event)]
        /\ sigma' = [sigma EXCEPT ![numAig] = order[3]]
        /\ UNCHANGED feux
        /\ UNCHANGED meta


Att_bf == 
    LET
        a == Head(meta.msg[1])
        id == <<a[1],a[2]>>
        event == Head(reg.E[id])
        order == Head(event)
        pos == id[1]
        jet == order[2]
        val == order[3]
        tid == CHOOSE i \in DOMAIN reg.H : reg.H[i][1] = id[1]
    IN 
        /\ meta.garde.state = "event"
        /\ Len(meta.msg[1]) /= 0
        /\ Len(event) > 0
        /\ order[1] = "att"
        /\ reg.J[jet] /= val
        /\ UNCHANGED gamma
        /\ rule' = "att_bf"
        /\ reg' = [reg EXCEPT !.W = reg.W \union {<<tid,pos,jet,val>>},
                              !.CP[tid] = Tail(reg.CP[tid]),
                              !.E[id][1] = Tail(event)]
        /\ UNCHANGED sigma
        /\ UNCHANGED feux
        /\ UNCHANGED meta
        
        
Att_af == 
    LET
        a == Head(meta.msg[1])
        id == <<a[1],a[2]>>
        event == Head(reg.E[id])
        order == Head(event)
        jet == order[2]
        val == order[3]
        tid == CHOOSE i \in DOMAIN reg.H : reg.H[i][1] = id[1]
        target == Head(Tail(reg.CP[tid]))
    IN
        /\ meta.garde.state = "event"
        /\ Len(meta.msg[1]) /= 0
        /\ Len(event) > 0
        /\ order[1] = "att"
        /\ reg.J[jet] = val
        /\ UNCHANGED gamma
        /\ rule' = "att_af"
        /\ reg' = [reg EXCEPT !.E[id][1] = Tail(event),
                              !.CP[tid] = Tail(reg.CP[tid])]
        /\ UNCHANGED sigma
        /\ UNCHANGED feux
        /\ meta' = [meta EXCEPT !.garde.requests = meta.garde.requests \o << <<target,"R">> >>]


Incr_bf ==
    LET
        i == Head(meta.msg[1])
        id == <<i[1],i[2]>>
        event == Head(reg.E[id])
        order == Head(event)
        jet == order[2]
        val == reg.J[jet]
    IN
        /\ meta.garde.state = "event"
        /\ Len(meta.msg[1]) /= 0
        /\ Len(event) > 0
        /\ order[1] = "incr"
        /\ ~IsWaiting(reg.W,jet,val+1) \*Personne n'attend encore
        /\ UNCHANGED gamma
        /\ rule' = "incr_bf"
        /\ reg' = [reg EXCEPT !.J[jet] = reg.J[jet]+1,
                              !.E[id][1] = Tail(event)]
        /\ UNCHANGED sigma
        /\ UNCHANGED feux
        /\ UNCHANGED meta


Incr_af ==
    LET
        a == Head(meta.msg[1])
        id == <<a[1],a[2]>>
        event == Head(reg.E[id])
        order == Head(event)
        jet == order[2]
        val == reg.J[jet]
        
        info_wait == getWaiting(reg.W,jet,val+1)
        id_wait == info_wait[1]
        target == Head(reg.CP[id_wait])
    IN
        /\ meta.garde.state = "event"
        /\ Len(meta.msg[1]) /= 0
        /\ Len(event) > 0
        /\ order[1] = "incr"
        /\ IsWaiting(reg.W,jet,val+1)
        /\ UNCHANGED gamma
        /\ rule' = "incr_af "
        /\ reg' = [reg EXCEPT !.J[jet] = reg.J[jet]+1,
                              !.W = {seq \in reg.W : seq /= info_wait},
                              !.E[id][1] = Tail(event)]
        /\ UNCHANGED sigma
        /\ UNCHANGED feux
        /\ meta' = [meta EXCEPT !.garde.requests = meta.garde.requests \o << <<target,"R">> >>]
        \*/\ PrintT(target)



Auth ==
    LET
        a == Head(meta.msg[1])
        id == <<a[1],a[2]>>
        event == Head(reg.E[id])
        order == Head(event)
        tid == CHOOSE i \in DOMAIN reg.H : reg.H[i][1] = id[1]
        target == Head(reg.CP[tid])
    IN
        /\ meta.garde.state = "event"
        /\ Len(meta.msg[1]) /= 0
        /\ Len(event) > 0
        /\ order[1] = "auth"
        /\ UNCHANGED gamma
        /\ rule' = "auth"
        /\ reg' = [reg EXCEPT !.E[id][1] = Tail(event),
                              !.CP[tid] = Tail(reg.CP[tid])]
        /\ UNCHANGED sigma
        /\ UNCHANGED feux
        /\ meta' = [meta EXCEPT !.garde.requests = meta.garde.requests \o << <<target,"R">> >>]



EndEvent ==
    LET
        a == Head(meta.msg[1])
        id == <<a[1],a[2]>>
        event == Head(reg.E[id])
    IN
        /\ meta.garde.state = "event"
        /\ Len(meta.msg[1]) /= 0
        /\ Len(event) = 0
        /\ UNCHANGED gamma
        /\ rule' = "EndEvent"
        /\ reg' = [reg EXCEPT !.E[id] = Tail(reg.E[id])]
        /\ UNCHANGED sigma
        /\ UNCHANGED feux
        /\ meta' = [meta EXCEPT !.garde.state = "update",
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
    /\ feux' = UpdateS(feux,reg.W,reg.CP)
    /\ meta' = [meta EXCEPT !.garde.state = "none"]
    \*/\ PrintT(gamma)
        
        


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
    /\  <>[] /\ gamma[1].pos = 3
             /\ gamma[1].dir = "*"
    /\  <>[] /\ gamma[2].pos = 1
             /\ gamma[2].dir = "*"

Safety == [] (gamma[1].pos /= gamma[2].pos)


Creep == <>[] (\A t \in DOMAIN reg.H : reg.H[t][1] = gamma[t].pos) \* cohérence entre 'vrai train' et 'train simulé'


\* Spec

Next == 
    \E i \in 1..Len(gamma) :
        \/ Start(gamma[i])
        \/ Until(gamma[i])
        \/ Until_cons(gamma[i])
        \/ ExitBlock(gamma[i])
        \/ EnterSwitch(gamma[i])
        \/ EnterBlock(gamma[i])
        \/ EnterBlock_cons(gamma[i])
        \/ Stop(gamma[i])
        \/ StartEvent
        \/ Turn
        \/ Incr_bf
        \/ Incr_af
        \/ Att_bf
        \/ Att_af
        \/ Auth
        \/ EndEvent
        \/ ReqUpdate
        \/ UpdateTL
        \/ IDLE
        

Spec == Init /\ [][Next]_<<gamma,reg,sigma,feux,meta,rule>> /\ WF_<<gamma,reg,sigma,feux,meta,rule>>(Next)
\* WF_ : Weak Fairness, "si une règle peut être appliquée, je l'applique"

set == {<<1,4,5,7>>,<<2,6,5,8>>}


Eval == Stalk(<< <<1,"R">>, <<3,"L">> >>, <<"d">>, <<2,"R">>) \*\E seq \in set : seq[1] = 2 \*SelectSeq(<< <<8,<<<<"">>, <<"">>, <<" ">>>>>>, <<2,<<<<"att">>>>>> >>, IsAttTurnInSeq)[1][1] \*"Hello" \o " World !"

=============================================================================
\* Modification History
\* Last modified Thu Jul 17 09:36:32 CEST 2025 by lucas
\* Created Fri May 09 16:46:37 CEST 2025 by lucas
