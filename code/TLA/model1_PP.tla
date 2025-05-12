----------------------------- MODULE model1_PP -----------------------------


EXTENDS Integers, TLC, Sequences\*, scenario (*
VARIABLE gamma, reg, rule, msg

\* Grands pas

train1 == [
    id |-> 1,
    pos |-> 1,
    dir |-> "*",
    prog |-> << <<"StartUntil", "R", 3>> >>,
    auth |-> 2,
    rel |-> 1
]

train2 == [
    id |-> 2,
    pos |-> 4,
    dir |-> "*",
    prog |-> << <<"StartUntil", "L", 1>> >>,
    auth |-> 0,
    rel |-> 1
]

events == <<
        << <<>>, <<>>, <<<<"turn",1,"v">>,<<"incr",2>>>> >>,
        << <<<<"att",2,1>>>>, <<>>, <<>> >> \* transformer "att(2,1)" en << "att",2,1 >>
     >>

nbCanton == 4 \* Nombre de canton du circuit
maxVal == 3 \* Valeur max que peut prendre un jeton

token == [x \in 1..nbCanton |-> 0]

wait == [x \in (1..nbCanton) \X (0..maxVal) |-> -1] 

switch == <<"d">>

repAuth == <<0,0>>

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
            E  |-> events,
            J  |-> token,
            S  |-> switch,
            W  |-> wait,
            A  |-> repAuth
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


IsAttInSeq(S) == 
    \E x \in DOMAIN S : 
        S[x][1] = "att" \/ S[x][1] = "turn" \* True si le tableau comporte une chaîne "att" ou "turn"


NextAtt(id, evs, evCourante) == \*evs : séquence d'events pour un train / evCourante : numéro de l'event courant
    LET 
        index == SelectInSeq(evs,IsAttInSeq)
        offset == Len(reg.E[id])-Len(evs)
    IN
        IF index /= 0 THEN (offset+index)-evCourante \*Il existe un prochain attendre
        ELSE Len(reg.E[id])-evCourante \*Il n'existe pas de prochain attendre (aller à la fin)

IsntEmpty(S) == Len(S) /= 0

\* règles
        \* Train
Start(T) == 
    /\ Len(T.prog) > 0
    /\ T.prog[1][1] = "StartUntil" 
    /\ T.prog[1][2] /= T.dir
    /\ gamma' = [gamma EXCEPT ![T.id].dir = T.prog[1][2]] \*![T.id].dir : T.id uniquement si T.id == pos dans gamma
    /\ rule ' = "start"
    /\ UNCHANGED reg
    /\ msg' = [msg EXCEPT ![1] = Append(msg[1],<<T.id,T.rel>>)]


Stop (T) ==
    /\ Len(T.prog) = 0
    /\ T.dir /= "*"
    /\ gamma' = [gamma EXCEPT ![T.id].dir = "*"]
    /\ rule' = "stop"
    /\ UNCHANGED <<reg,msg>>


Until(T) == 
    LET
        id == T.id
        order == Head(T.prog)
        nextC == Suiv(T.pos,T.dir, reg.S)
        auth == T.auth
    IN
        /\ Len(T.prog) > 0
        /\ order[2] = T.dir 
        /\ auth /= 0
        /\ order[1] = "StartUntil"
        /\ nextC /= -1
        /\ order[3] /= nextC
        /\ gamma' = [gamma EXCEPT 
                            ![id].pos = nextC,
                            ![id].auth = T.auth-1,
                            ![id].rel = T.rel+1]
        /\ rule' = "until"
        /\ UNCHANGED reg
        /\ IF Len(reg.E[id][T.rel+1]) /= 0 THEN 
                msg' = [msg EXCEPT ![1] = Append(msg[1],<<id,T.rel+1>>)]
           ELSE \* pas d'event
                UNCHANGED msg
            


Until_cons(T) == 
    LET
        id == T.id
        order == Head(T.prog)
        nextC == Suiv(T.pos,T.dir, reg.S)
        auth == T.auth
    IN
        /\ Len(T.prog) > 0
        /\ order[2] = T.dir
        /\ auth /= 0
        /\ order[1] = "StartUntil" 
        /\ nextC /= -1
        /\ order[3] = nextC
        /\ gamma' = [gamma EXCEPT 
                            ![T.id].pos = nextC,
                            ![T.id].prog = Tail(T.prog),
                            ![id].auth = T.auth-1,
                            ![id].rel = T.rel+1]
        /\ rule' = "until_cons"
        /\ UNCHANGED reg
        /\ IF Len(reg.E[id][T.rel+1]) /= 0 THEN 
                msg' = [msg EXCEPT ![1] = Append(msg[1],<<id,T.rel+1>>)]
           ELSE \* pas d'event
                UNCHANGED msg

Recv(T) ==
    LET
        id == Head(msg[2])[1]
        suppl == Head(msg[2])[2]
    IN
        /\ Len(msg[2]) /= 0
        /\ T.id = id
        /\ gamma' = [gamma EXCEPT ![id].auth = gamma[id].auth+suppl]
        /\ UNCHANGED reg
        /\ rule' = "recv message"
        /\ msg' = [msg EXCEPT ![2] = Tail(msg[2])]


        \* Regulateur
Turn == 
    LET
        id == Head(msg[1])[1]
        rel == Head(msg[1])[2]
        event == reg.E[id][rel] \* Sequence d'ordre de l'event
        order == Head(event)
        numAig == order[2]
        subseqEv == SubSeq(reg.E[id],rel+1,Len(reg.E[id]))
    IN
        /\ Len(msg[1]) /= 0
        /\ Len(event) > 0
        /\ order[1] = "turn"
        /\ numAig <= Len(reg.S)
        /\ numAig >= 0
        /\ UNCHANGED gamma
        /\ rule' = "turn"
        /\ reg' = [reg EXCEPT !.S[numAig] = order[3],
                              !.A[id] = NextAtt(id,subseqEv,rel), \*Prendre ne compte turn pour NextAtt
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
    IN
        /\ Len(msg[1]) /= 0
        /\ Len(event) > 0
        /\ order[1] = "att"
        /\ reg.J[jet] = val
        /\ UNCHANGED gamma
        /\ rule' = "att_af"
        /\ reg' = [reg EXCEPT !.W[jet,val] = id,
                              !.A[id] = NextAtt(id,subseqEv,rel),
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
        rel_wait == gamma[id_wait].rel
        subseqEv == SubSeq(reg.E[id_wait],rel_wait,Len(reg.E[id_wait]))
    IN
        /\ Len(msg[1]) /= 0
        /\ Len(event) > 0
        /\ order[1] = "incr"
        /\ id_wait /= -1
        /\ UNCHANGED gamma
        /\ rule' = "incr_af"
        /\ reg' = [reg EXCEPT !.J[jet] = reg.J[jet]+1,
                              !.A[id_wait] = NextAtt(id_wait,subseqEv,rel_wait),
                              !.E[id][rel] = Tail(event)]
        /\ UNCHANGED msg

SendAuth ==
    LET
        id == Head(msg[1])[1]
        rel == Head(msg[1])[2]
        event == reg.E[id][rel] \* Sequence d'ordre de l'event
    IN
        /\ Len(msg[1]) /= 0
        /\ Len(event) = 0
        /\ UNCHANGED gamma
        /\ rule' = "SendAuth"
        /\ reg' = [reg EXCEPT !.A = [x \in (1..Len(gamma)) |-> 0] ]
        /\ msg' = [msg EXCEPT ![1] = Tail(msg[1]),
                              ![2] = msg[2] \o SelectSeq([x \in 1..Len(gamma) |-> IF reg.A[x] /= 0 THEN <<x,reg.A[x]>> ELSE <<>>],IsntEmpty) ]

IDLE ==
    \A t \in 1..Len(gamma):
        /\ Len(gamma[t].prog) = 0
        /\ gamma[t].dir = "*"
    /\ Len(msg[1]) = 0
    /\ Len(msg[2]) = 0   
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
        \/ Recv(gamma[i])
        \/ Turn
        \/ Incr_bf
        \/ Incr_af
        \/ Att_bf
        \/ Att_af
        \/ SendAuth
        \/ IDLE
        

Spec == Init /\ [][Next]_<<gamma,reg, rule, msg>> /\ WF_<<gamma,reg,rule,msg>>(Next)
\* WF_ : Weak Fairness, "si une règle peut être appliquée, je l'applique"


Eval == "Hello" \o " World !"

=============================================================================
\* Modification History
\* Last modified Mon May 12 09:55:52 CEST 2025 by lucas
\* Created Fri May 09 16:46:37 CEST 2025 by lucas
