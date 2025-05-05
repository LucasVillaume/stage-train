------------------------------- MODULE model0 -------------------------------


EXTENDS Integers, TLC, Sequences
VARIABLE gamma, reg, rule

train1 == [
    id |-> 1,
    pos |-> "1",
    dir |-> "*",
    prog |-> <<"StartUntil(R,3)">>
]

train2 == [
    id |-> 2,
    pos |-> "4",
    dir |-> "*",
    prog |-> <<"StartUntil(L,1)">>
]
  
token == <<0,0,0,0>>

auths == <<2,0>>

events == <<
        << <<>>, <<>>, <<"turn(1,v)","incr(2)">> >>,
        << <<"att(2,1)">>, <<>>, <<>> >>
     >>

nextEv == <<1,1>>

wait == [x \in (1..4) \X (0..2) |-> -1] \* créée chaque clé (jeton, valeur) pour jeton de 1 à 4 et val de 0 à 2

switch == <<"d">>


Suiv(pos, dir, S) == IF pos = "1" /\ dir = "R"               THEN "2"
                ELSE IF pos = "2" /\ dir = "R" /\ S[1] = "d" THEN "3"
                ELSE IF pos = "2" /\ dir = "R" /\ S[1] = "v" THEN "4"
                ELSE IF pos = "2" /\ dir = "L"               THEN "1"
                ELSE IF pos = "3" /\ dir = "L" /\ S[1] = "d" THEN "2"
                ELSE IF pos = "4" /\ dir = "L" /\ S[1] = "v" THEN "2"
                ELSE "-1"

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

IsAttInSeq(S) == \E x \in DOMAIN S : Len(S[x]) > 3 /\ SubSeq(S[x],1,3) = "att" \* True si le tableau comporte une chaîne "att"

NextAtt(id, evs, evCourante) == \*evs : séquence d'events pour un train / evCourante : numéro de l'event courant
    LET 
        index == SelectInSeq(evs,IsAttInSeq)
        offset == Len(reg.E[id])-Len(evs)
    IN
        IF index /= 0 THEN (offset+index)-evCourante \*Il existe un prochain attendre
        ELSE Len(reg.E[id])-evCourante \*Il n'existe pas de prochain attendre (aller à la fin)



\* règles
\*n : position du train dans gamma

Start(T) == 
    /\ Len(T.prog) > 0
    /\ SubSeq(T.prog[1],1,10) = "StartUntil"
    /\ CharAt(T.prog[1],12) /= T.dir
    /\ gamma' = [gamma EXCEPT ![T.id].dir = CharAt(T.prog[1],12)] \*![T.id].dir : T.id uniquement si T.id == pos dans gamma
    /\ rule ' = "start"
    /\ UNCHANGED reg

Stop (T) ==
    /\ Len(T.prog) = 0
    /\ T.dir /= "*"
    /\ gamma' = [gamma EXCEPT ![T.id].dir = "*"]
    /\ rule' = "stop"
   /\ UNCHANGED reg


Until(T) == 
    LET
        numEv == reg.Ne[T.id]
        id == T.id
        event == reg.E[id][numEv]
        order == Head(T.prog)
        nextC == Suiv(T.pos,T.dir, reg.S)
        auth == reg.A[id]
    IN
        /\ Len(T.prog) > 0
        /\ Len(event) = 0
        /\ CharAt(T.prog[1],12) = T.dir
        /\ auth /= 0
        /\ SubSeq(order,1,10) = "StartUntil"
        /\ nextC /= "-1"
        /\ nextC /= CharAt(order,14)
        /\ gamma' = [gamma EXCEPT ![id].pos = nextC]
        /\ rule' = "until"
        /\ reg' = [reg EXCEPT !.Ne[id] = numEv+1,
                              !.A[id] = auth-1]


Until_cons(T) == 
    LET
        numEv == reg.Ne[T.id]
        id == T.id
        event == reg.E[id][numEv]
        order == Head(T.prog)
        nextC == Suiv(T.pos,T.dir, reg.S)
        auth == reg.A[id]
    IN
        /\ Len(T.prog) > 0
        /\ Len(event) = 0
        /\ CharAt(T.prog[1],12) = T.dir
        /\ auth /= 0
        /\ SubSeq(order,1,10) = "StartUntil"
        /\ nextC /= "-1"
        /\ nextC = CharAt(order,14)
        /\ gamma' = [gamma EXCEPT 
                            ![T.id].pos = nextC,
                            ![T.id].prog = Tail(T.prog)]
        /\ rule' = "until_cons"
        /\ reg' = [reg EXCEPT !.Ne[id] = numEv+1,
                              !.A[id] = auth-1]


Turn(T) ==
    LET
        id == T.id
        numEv == reg.Ne[id] \* numéro de l'event courant
        event == reg.E[id][numEv] \* Sequence d'ordre de l'event
        order == Head(event)
        numAig == StrToI(CharAt(order,6))
    IN
        /\ Len(event) > 0
        /\ SubSeq(order,1,4) = "turn"
        /\ numAig <= Len(reg.S) 
        /\ numAig >= 0
        /\ UNCHANGED gamma
        /\ rule' = "turn"
        /\ reg' = [reg EXCEPT !.S[numAig] = CharAt(order,8),
                              !.E[id][numEv] = Tail(event)]

Att_bf(T) ==
    LET
        id == T.id
        numEv == reg.Ne[id] \* numéro de l'event courant
        event == reg.E[id][numEv] \* Sequence d'ordre de l'event
        order == Head(event)
        jet == StrToI(CharAt(order,5))
        val == StrToI(CharAt(order,7))
    IN
        /\ Len(event) > 0
        /\ SubSeq(order,1,3) = "att"
        /\ reg.J[jet] /= val
        /\ UNCHANGED gamma
        /\ rule' = "att_bf"
        /\ reg' = [reg EXCEPT !.W[jet,val] = id,
                              !.E[id][numEv] = Tail(event)]

Att_af(T) ==
    LET
        id == T.id
        numEv == reg.Ne[id] \* numéro de l'event courant
        event == reg.E[id][numEv] \* Sequence d'ordre de l'event
        order == Head(event)
        jet == StrToI(CharAt(order,5))
        val == StrToI(CharAt(order,7))
        subseqEv == SubSeq(reg.E[id],numEv+1,Len(reg.E[id]))
    IN
        /\ Len(event) > 0
        /\ SubSeq(order,1,3) = "att"
        /\ reg.J[jet] = val
        /\ UNCHANGED gamma
        /\ rule' = "att_af"
        /\ reg' = [reg EXCEPT !.W[jet,val] = id,
                              !.A[id] = NextAtt(id,subseqEv,numEv),
                              !.E[id][numEv] = Tail(event)]

Incr_bf(T) ==
    LET
        id == T.id
        numEv == reg.Ne[id] \* numéro de l'event courant
        event == reg.E[id][numEv] \* Sequence d'ordre de l'event
        order == Head(event)
        jet == StrToI(CharAt(order,6))
        val == reg.J[jet]
        id_wait == reg.W[jet,val+1]
    IN
        /\ Len(event) > 0
        /\ SubSeq(order,1,4) = "incr"
        /\ id_wait = -1
        /\ UNCHANGED gamma
        /\ rule' = "incr_bf"
        /\ reg' = [reg EXCEPT !.J[jet] = reg.J[jet]+1,
                              !.E[id][numEv] = Tail(event)]
                              
                              
Incr_af(T) ==
    LET
        id == T.id
        numEv == reg.Ne[id] \* numéro de l'event courant
        event == reg.E[id][numEv] \* Sequence d'ordre de l'event
        order == Head(event)
        jet == StrToI(CharAt(order,6))
        val == reg.J[jet]
        id_wait == reg.W[jet,val+1]
        numEv_wait == reg.Ne[id_wait]
        subseqEv == SubSeq(reg.E[id_wait],numEv_wait,Len(reg.E[id_wait]))
    IN
        /\ Len(event) > 0
        /\ SubSeq(order,1,4) = "incr"
        /\ id_wait /= -1
        /\ UNCHANGED gamma
        /\ rule' = "incr_af"
        /\ reg' = [reg EXCEPT !.J[jet] = reg.J[jet]+1,
                              !.A[id_wait] = NextAtt(id_wait,subseqEv,numEv_wait),
                              !.E[id][numEv] = Tail(event)]


\* Propriétés


Liveness ==
    /\  <>[] (gamma[1].pos = "3"
            /\ gamma[1].dir = "*")
    /\  <>[] (gamma[2].pos = "1"
            /\ gamma[2].dir = "*")

Safety == [] (gamma[1].pos /= gamma[2].pos)


\* Spec


Init == 
    /\ gamma = <<train1,train2>>
    /\ reg = [
            J  |-> token,
            E  |-> events,
            A  |-> auths,
            Ne |-> nextEv,
            W  |-> wait,
            S  |-> switch
       ]
    /\ rule = ""

Next == 
    \E i \in 1..Len(gamma) :
        \/ Start(gamma[i])
        \/ Until(gamma[i])
        \/ Until_cons(gamma[i])
        \/ Stop(gamma[i])
        \/ Turn(gamma[i])
        \/ Att_bf(gamma[i])
        \/ Att_af(gamma[i])
        \/ Incr_bf(gamma[i])
        \/ Incr_af(gamma[i])
        

Spec == Init /\ [][Next]_<<gamma,reg, rule>>



\*Eval == ""



=============================================================================
\* Modification History
\* Last modified Mon May 05 11:19:20 CEST 2025 by lucas
\* Created Tue Apr 29 13:37:40 CEST 2025 by lucas
