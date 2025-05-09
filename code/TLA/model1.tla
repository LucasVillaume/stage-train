------------------------------- MODULE model1 -------------------------------


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

token == <<0,0,0,0>>

events == <<
        << <<>>, <<>>, <<<<"turn",1,"v">>,<<"incr",2>>>> >>,
        << <<<<"att",2,1>>>>, <<>>, <<>> >> \* transformer "att(2,1)" en << "att",2,1 >>
     >>

nbCanton == 4 \* Nombre de canton du circuit
maxVal == 3 \* Valeur max que peut prendre un jeton

wait == [x \in (1..nbCanton) \X (0..maxVal) |-> -1] 

switch == <<"d">>


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
            W  |-> wait
       ]
    /\ rule = "" \* Mesure de débug, pas présent dans le modèle
    /\ msg = << <<>>, <<>> >>

\* *)
\*Init == Init_S4
\*Suiv(pos, dir, S) == Suiv_S4(pos, dir, S)


\* Utilitaire


CharAt(str, pos) == SubSeq(str, pos, pos)
             
StrToI(str) == IF str = "0" THEN 0
          ELSE IF str = "1" THEN 1
          ELSE IF str = "2" THEN 2
          ELSE IF str = "3" THEN 3
          ELSE IF str = "4" THEN 4
          ELSE -1

Min(S) == CHOOSE x \in S : \A y \in S : x =< y


SelectInSeq(seq, Test(_)) == 
  LET I == { i \in 1..Len(seq) : Test(seq[i]) }
  IN IF I # {} THEN Min(I) ELSE 0


IsAttInSeq(S) == 
    \E x \in DOMAIN S : 
        S[x][1] = "att" \* True si le tableau comporte une chaîne "att"


NextAtt(id, evs, evCourante) == \*evs : séquence d'events pour un train / evCourante : numéro de l'event courant
    LET 
        index == SelectInSeq(evs,IsAttInSeq)
        offset == Len(reg.E[id])-Len(evs)
    IN
        IF index /= 0 THEN (offset+index)-evCourante \*Il existe un prochain attendre
        ELSE Len(reg.E[id])-evCourante \*Il n'existe pas de prochain attendre (aller à la fin)

Apply(id, rel) ==
    IF id = 1 /\ rel = 3  THEN 
        /\ UNCHANGED gamma
        /\ reg' = [reg EXCEPT !.S[1] = "v",
                              !.E[id][rel] = <<>>,
                              !.J[2] = reg.J[2]+1]
        /\ IF reg.W[2,1] = -1 THEN
            /\ rule' = "turn(1,v) et incr_bf(2)"
            /\ msg' = [msg EXCEPT ![1] = Tail(msg[1])]
           ELSE   
            /\ rule' = "turn(1,v) et incr_af(2)"
            /\ msg' = [msg EXCEPT ![1] = Tail(msg[1]),
                                  ![2] = Append(msg[2],<<2,2>>)]
                                  
    ELSE IF id = 2 /\ rel = 1  THEN 
        /\ UNCHANGED gamma
        /\ reg' = [reg EXCEPT !.W[2,1] = id,
                              !.E[id][rel] = <<>>]
        /\ IF reg.J[2] = -1 THEN
            /\ rule' = "att_bf(2,1)"
            /\ msg' = [msg EXCEPT ![1] = Tail(msg[1])]
           ELSE
            /\ rule' = "att_af(2,1)"
            /\ msg' = [msg EXCEPT ![1] = Tail(msg[1]),
                                  ![2] = Append(msg[2],<<id,2>>)]
                
    ELSE
        /\ reg' = [reg EXCEPT !.E[id][rel] = <<>>] \*Dépile l'event
        /\ UNCHANGED gamma
        /\ rule' = "event null"
        /\ msg' = [msg EXCEPT ![1] = Tail(msg[1])] \*Dépile le message



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
        /\ msg' = [msg EXCEPT ![1] = Append(msg[1],<<id,T.rel+1>>)]


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
        /\ msg' = [msg EXCEPT ![1] = Append(msg[1],<<id,T.rel+1>>)]

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

Event == 
    LET
        id == Head(msg[1])[1]
        rel == Head(msg[1])[2]
    IN
        /\ Len(msg[1]) /= 0
        /\ Apply(id,rel)


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
        \/ Event
        \/ IDLE
        

Spec == Init /\ [][Next]_<<gamma,reg, rule, msg>> /\ WF_<<gamma,reg,rule,msg>>(Next)


Eval == "Hello" \o " World !"


=============================================================================
\* Modification History
\* Last modified Fri May 09 16:42:46 CEST 2025 by lucas
\* Created Wed May 07 09:59:02 CEST 2025 by lucas
