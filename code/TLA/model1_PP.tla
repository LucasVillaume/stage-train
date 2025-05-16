----------------------------- MODULE model1_PP -----------------------------


EXTENDS Integers, TLC, Sequences\*, scenario_m1 (*
VARIABLE gamma, reg, rule, msg


train1 == [
    id |-> 1,
    pos |-> 1,
    dir |-> "*",
    prog |-> << <<"StartUntil", "R", 3>> >>,
    rel |-> 1
]

train2 == [
    id |-> 2,
    pos |-> 4,
    dir |-> "*",
    prog |-> << <<"StartUntil", "L", 1>> >>,
    rel |-> 1
]

events == <<
        << <<>>, <<>>, <<<<"turn",1,"v",2>>,<<"incr",2>>>> >>,
        << <<<<"att",2,1>>>>, <<>>, <<>> >>
     >>

nbCanton == 4 \* Nombre de canton du circuit
maxVal == 3 \* Valeur max que peut prendre un jeton

token == [x \in 1..nbCanton |-> 0]

wait == [x \in (1..nbCanton) \X (0..maxVal) |-> -1] 

switch == <<"d">>

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
            G |-> FALSE,
            F |-> [traffic_lights EXCEPT ![4,"R"] = "R",
                                         ![4,"L"] = "R"]
       ]
    /\ rule = "" \* Mesure de débug, pas présent dans le modèle
    /\ msg = << <<>>, <<>> >>

\* *)
\*Init == Init_S4
\*Suiv(pos, dir, S) == Suiv_S4(pos, dir, S)


\* Utilitaire

Min(S) == CHOOSE x \in S : \A y \in S : x =< y


SelectInSeq(seq, Test(_)) == 
  LET I == { i \in 1..Len(seq) : Test(seq[i]) }
  IN IF I # {} THEN Min(I) ELSE 0


IsAttTurnInSeq(S) == 
    \E x \in DOMAIN S : 
        S[x][1] = "att" \/ S[x][1] = "turn" \* True si le tableau comporte une chaîne "att" ou "turn"

IsAttInSeq(S) == 
    \E x \in DOMAIN S : 
        S[x][1] = "att"\* True si le tableau comporte une chaîne "att"

NextAtt(id, evs, evCourante) == \*evs : séquence d'events pour un train / evCourante : numéro de l'event courant
    LET 
        index == SelectInSeq(evs,IsAttTurnInSeq)
        offset == Len(reg.E[id])-Len(evs)
    IN
        IF index /= 0 THEN (offset+index)-evCourante \*Il existe un prochain attendre
        ELSE Len(reg.E[id])-evCourante \*Il n'existe pas de prochain attendre (aller à la fin)


IsntEmpty(S) == Len(S) /= 0


RECURSIVE FindSection(_,_,_,_)
FindSection(pos,dir,cpt,S) ==
    LET
        nextPos == Suiv(pos,dir,S)
    IN 
        IF cpt = 1 THEN 
            nextPos
        ELSE
            FindSection(nextPos,dir,cpt-1,S)
                
            

\* règles
        \* Train
        
Start(T) == 
    /\ Len(T.prog) > 0
    /\ reg.G = FALSE
    /\ T.prog[1][1] = "StartUntil" 
    /\ T.prog[1][2] /= T.dir
    /\ gamma' = [gamma EXCEPT ![T.id].dir = T.prog[1][2]]
    /\ rule ' = "start"
    /\ UNCHANGED reg
    /\ IF Len(reg.E[T.id][T.rel]) /= 0 THEN \* Pas important, juste une petite optimisation
            msg' = [msg EXCEPT ![1] = Append(msg[1],<<T.id,T.rel>>)]
       ELSE \* pas d'event
            UNCHANGED msg

Stop (T) ==
    /\ Len(T.prog) = 0
    /\ reg.G = FALSE
    /\ T.dir /= "*"
    /\ gamma' = [gamma EXCEPT ![T.id].dir = "*"]
    /\ rule' = "stop"
    /\ UNCHANGED reg
    /\ IF Len(reg.E[T.id][T.rel]) /= 0 THEN \* Pas important, juste une petite optimisation
            msg' = [msg EXCEPT ![1] = Append(msg[1],<<T.id,T.rel>>)]
       ELSE \* pas d'event
            UNCHANGED msg


Until(T) == 
    LET
        id == T.id
        order == Head(T.prog)
        nextC == Suiv(T.pos,T.dir, reg.S)
    IN
        /\ Len(T.prog) > 0
        /\ reg.G = FALSE
        /\ order[2] = T.dir 
        /\ reg.F[T.pos,T.dir] = "V"
        /\ order[1] = "StartUntil"
        /\ nextC /= -1
        /\ order[3] /= nextC
        /\ gamma' = [gamma EXCEPT 
                            ![id].pos = nextC,
                            ![id].rel = T.rel+1]
        /\ rule' = "until"
        /\ UNCHANGED reg
        /\ IF Len(reg.E[id]) >= T.rel+1 THEN
                /\ IF Len(reg.E[id][T.rel+1]) /= 0 THEN 
                        msg' = [msg EXCEPT ![1] = Append(msg[1],<<id,T.rel+1>>)]
                   ELSE \* pas d'event
                        UNCHANGED msg
          ELSE
            UNCHANGED msg



Until_cons(T) == 
    LET
        id == T.id
        order == Head(T.prog)
        nextC == Suiv(T.pos,T.dir, reg.S)
    IN
        /\ Len(T.prog) > 0
        /\ reg.G = FALSE
        /\ order[2] = T.dir
        /\ reg.F[T.pos,T.dir] = "V"
        /\ order[1] = "StartUntil" 
        /\ nextC /= -1
        /\ order[3] = nextC
        /\ gamma' = [gamma EXCEPT 
                            ![T.id].pos = nextC,
                            ![T.id].prog = Tail(T.prog),
                            ![id].rel = T.rel+1]
        /\ rule' = "until_cons"
        /\ UNCHANGED <<reg,msg>>


        \* Regulateur
        
StartEvent == \*Simuler une approche grands pas
    /\ reg.G = FALSE
    /\ Len(msg[1]) /= 0
    /\ UNCHANGED gamma
    /\ reg' = [reg EXCEPT !.G = TRUE]
    /\ rule' = "StartEvent"
    /\ UNCHANGED msg
        
Turn_self == 
    LET
        id == Head(msg[1])[1]
        rel == Head(msg[1])[2]
        event == reg.E[id][rel] \* Sequence d'ordre de l'event
        order == Head(event)
        numAig == order[2]
        id_turn == order[4] \*train concerné par le turn
        rel_turn == gamma[id_turn].rel \* position relative du train concerné par le turn
        subseqEv == SubSeq(reg.E[id_turn],rel_turn+1,Len(reg.E[id_turn]))
        cptAuth == NextAtt(id,subseqEv,rel)
        pos == gamma[id_turn].pos \* intervention divine (voir pour corriger ça)
        dir == gamma[id_turn].dir \* intervention divine (voir pour corriger ça)
        nextS == [reg.S EXCEPT ![numAig] = order[3]] \* peu élégent mais limitation technique
        target == FindSection(pos, dir, cptAuth, nextS)
    IN
        /\ reg.G = TRUE
        /\ Len(msg[1]) /= 0
        /\ Len(event) > 0
        /\ order[1] = "turn"
        /\ numAig <= Len(reg.S)
        /\ numAig >= 0
        /\ id = id_turn
        /\ UNCHANGED gamma
        /\ rule' = "turn_self"
        /\ reg' = [reg EXCEPT !.S[numAig] = order[3],
                              !.F[target,"L"] = "R",
                              !.F[target,"R"] = "R",
                              !.F[pos,"L"]    = "V",
                              !.F[pos,"R"]    = "V",
                              !.E[id][rel] = Tail(event)]
        /\ UNCHANGED msg

Turn_other == 
    LET
        id == Head(msg[1])[1]
        rel == Head(msg[1])[2]
        event == reg.E[id][rel] \* Sequence d'ordre de l'event
        order == Head(event)
        numAig == order[2]
        id_turn == order[4] \*train concerné par le turn
    IN
        /\ reg.G = TRUE
        /\ Len(msg[1]) /= 0
        /\ Len(event) > 0
        /\ order[1] = "turn"
        /\ numAig <= Len(reg.S)
        /\ numAig >= 0
        /\ id /= id_turn
        /\ UNCHANGED gamma
        /\ rule' = "turn_other"
        /\ reg' = [reg EXCEPT !.S[numAig] = order[3],
                              !.E[id][rel] = Tail(event)]
        /\ UNCHANGED msg

Att_bf == 
    LET
        id == Head(msg[1])[1]
        rel == Head(msg[1])[2]
        event == reg.E[id][rel] \* Sequence d'ordre de l'event
        order == Head(event)
        jet == order[2]
        val == order[3]
    IN 
        /\ reg.G = TRUE
        /\ Len(msg[1]) /= 0
        /\ Len(event) > 0
        /\ order[1] = "att"
        /\ reg.J[jet] /= val
        /\ UNCHANGED gamma
        /\ rule' = "att_bf"
        /\ reg' = [reg EXCEPT !.W[jet,val] = id,
                              !.E[id][rel] = Tail(event)]
        /\ UNCHANGED msg

Att_af == 
    LET
        id == Head(msg[1])[1]
        rel == Head(msg[1])[2]
        event == reg.E[id][rel] \* Sequence d'ordre de l'event
        order == Head(event)
        jet == order[2]
        val == order[3]
        subseqEv == SubSeq(reg.E[id],rel+1,Len(reg.E[id]))
        cptAuth == NextAtt(id,subseqEv,rel)
        dir == gamma[id].dir \* intervention divine, voir pour corriger ça
        pos == gamma[id].pos \* intervention divine, voir pour corriger ça
        target == FindSection(pos,dir,cptAuth,reg.S)
    IN
        /\ reg.G = TRUE
        /\ Len(msg[1]) /= 0
        /\ Len(event) > 0
        /\ order[1] = "att"
        /\ reg.J[jet] = val
        /\ UNCHANGED gamma
        /\ rule' = "att_af"
        /\ reg' = [reg EXCEPT !.W[jet,val] = id,
                              !.F[target,"L"] = "R",
                              !.F[target,"R"] = "R",
                              !.F[pos,"L"]    = "V",
                              !.F[pos,"R"]    = "V",
                              !.E[id][rel] = Tail(event)]
        /\ UNCHANGED msg

Incr_bf ==
    LET
        id == Head(msg[1])[1]
        rel == Head(msg[1])[2]
        event == reg.E[id][rel] \* Sequence d'ordre de l'event
        order == Head(event)
        jet == order[2]
        val == reg.J[jet]
        id_wait == reg.W[jet,val+1]
    IN
        /\ reg.G = TRUE
        /\ Len(msg[1]) /= 0
        /\ Len(event) > 0
        /\ order[1] = "incr"
        /\ id_wait = -1
        /\ UNCHANGED gamma
        /\ rule' = "incr_bf"
        /\ reg' = [reg EXCEPT !.J[jet] = reg.J[jet]+1,
                              !.E[id][rel] = Tail(event)]
        /\ UNCHANGED msg

Incr_af ==
    LET
        id == Head(msg[1])[1]
        rel == Head(msg[1])[2]
        event == reg.E[id][rel] \* Sequence d'ordre de l'event
        order == Head(event)
        jet == order[2]
        val == reg.J[jet]
        id_wait == reg.W[jet,val+1]
        rel_wait == gamma[id_wait].rel  \* intervention divine, voir pour corriger ça
        subseqEv == SubSeq(reg.E[id_wait],rel_wait,Len(reg.E[id_wait]))
        cptAuth == NextAtt(id_wait,subseqEv,rel_wait)
        dir == gamma[id_wait].dir \* intervention divine, voir pour corriger ça
        pos == gamma[id_wait].pos \* intervention divine, voir pour corriger ça
        target == FindSection(pos,dir,cptAuth,reg.S)
    IN
        /\ reg.G = TRUE
        /\ Len(msg[1]) /= 0
        /\ Len(event) > 0
        /\ order[1] = "incr"
        /\ id_wait /= -1
        /\ UNCHANGED gamma
        /\ rule' = "incr_af "
        /\ reg' = [reg EXCEPT !.J[jet] = reg.J[jet]+1,
                              !.F[target,"L"] = "R",
                              !.F[target,"R"] = "R",
                              !.F[pos,"L"]    = "V",
                              !.F[pos,"R"]    = "V",
                              !.E[id][rel] = Tail(event)]
        /\ UNCHANGED msg

EndEvent ==
    LET
        id == Head(msg[1])[1]
        rel == Head(msg[1])[2]
        event == reg.E[id][rel] \* Sequence d'ordre de l'event
    IN
        /\ reg.G = TRUE
        /\ Len(msg[1]) /= 0
        /\ Len(event) = 0
        /\ UNCHANGED gamma
        /\ rule' = "EndEvent"
        /\ reg' = [reg EXCEPT !.G = FALSE]
        /\ msg' = [msg EXCEPT ![1] = Tail(msg[1])]


IDLE ==
    \A t \in 1..Len(gamma):
        /\ Len(gamma[t].prog) = 0
        /\ gamma[t].dir = "*"
    /\ Len(msg[1]) = 0
    /\ UNCHANGED gamma
    /\ rule' = "IDLE"
    /\ UNCHANGED reg
    /\ UNCHANGED msg

\* Propriétés

Liveness == 
    /\  <>[] /\ gamma[1].pos = 3
             /\ gamma[1].dir = "*"
    /\  <>[] /\ gamma[2].pos = 1
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
        \/ Turn_self
        \/ Turn_other
        \/ Incr_bf
        \/ Incr_af
        \/ Att_bf
        \/ Att_af
        \/ EndEvent
        \/ IDLE
        

Spec == Init /\ [][Next]_<<gamma,reg,rule,msg>> /\ WF_<<gamma,reg,rule,msg>>(Next)
\* WF_ : Weak Fairness, "si une règle peut être appliquée, je l'applique"

Eval == [x \in (1..3) \X {"A","B"} |-> -1] \*"Hello" \o " World !"

=============================================================================
\* Modification History
\* Last modified Fri May 16 09:56:07 CEST 2025 by lucas
\* Created Fri May 09 16:46:37 CEST 2025 by lucas
