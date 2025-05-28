----------------------------- MODULE model1 -----------------------------


EXTENDS Integers, TLC, Sequences, composition

\* Circuit
Suiv(pos, dir, S) ==   IF pos = 1 /\ dir = "L" /\ S[1] = "d" /\ S[2] = "v" THEN 3
                     ELSE IF pos = 2 /\ dir = "L" /\ S[1] = "v" /\ S[2] = "v" THEN 3
                     ELSE IF pos = 3 /\ dir = "L" /\ S[3] = "d"               THEN 7
                     ELSE IF pos = 3 /\ dir = "L" /\ S[3] = "v"               THEN 8
                     ELSE IF pos = 3 /\ dir = "R" /\ S[2] = "d"               THEN 4
                     ELSE IF pos = 3 /\ dir = "R" /\ S[1] = "d" /\ S[2] = "v" THEN 1
                     ELSE IF pos = 3 /\ dir = "R" /\ S[1] = "v" /\ S[2] = "v" THEN 2
                     ELSE IF pos = 4 /\ dir = "L" /\ S[2] = "d"               THEN 3
                     ELSE IF pos = 4 /\ dir = "R" /\ S[5] = "d"               THEN 5
                     ELSE IF pos = 4 /\ dir = "R" /\ S[5] = "v"               THEN 6
                     ELSE IF pos = 5 /\ dir = "L" /\ S[5] = "d"               THEN 4
                     ELSE IF pos = 5 /\ dir = "R" /\ S[4] = "d"               THEN 7
                     ELSE IF pos = 6 /\ dir = "L" /\ S[5] = "v"               THEN 4
                     ELSE IF pos = 6 /\ dir = "R" /\ S[4] = "v"               THEN 7
                     ELSE IF pos = 7 /\ dir = "L" /\ S[4] = "d"               THEN 5
                     ELSE IF pos = 7 /\ dir = "L" /\ S[4] = "v"               THEN 6
                     ELSE IF pos = 7 /\ dir = "R" /\ S[3] = "d"               THEN 3
                     ELSE IF pos = 8 /\ dir = "R" /\ S[3] = "v"               THEN 3
                     ELSE -1


\* Utilitaire

Min(S) == CHOOSE x \in S : \A y \in S : x =< y

IsAttTurnInSeq(S) == 
    \E x \in DOMAIN S[2] : 
        S[2][x][1] = "att" \/ S[2][x][1] = "turn" \* True si le tableau comporte une chaîne "att" ou "turn"

NextAttTurn(id, evs) == \*evs : séquence d'events pour un train / evCourante : numéro de l'event courant
    LET 
        res == SelectSeq(evs,IsAttTurnInSeq)
    IN
        IF Len(res) /= 0 THEN res[1][1]\*Il existe un prochain attendre
        ELSE evs[Len(evs)][1]\*Il n'existe pas de prochain attendre (aller à la fin)

\* règles
        \* Train
        
Start(T) == 
    LET
        event == Head(reg.E[T.id])
    IN
        /\ Len(T.prog) > 0
        /\ reg.G = FALSE
        /\ T.prog[1][1] = "StartUntil"
        /\ T.prog[1][2] /= T.dir
        /\ gamma' = [gamma EXCEPT ![T.id].dir = T.prog[1][2]]
        /\ rule ' = "start"
        /\ UNCHANGED reg
        /\ msg' = [msg EXCEPT ![1] = Append(msg[1],<<T.id,T.pos>>)]

Stop (T) ==
    LET
        event == Head(reg.E[T.id])
    IN
        /\ Len(T.prog) = 0
        /\ reg.G = FALSE
        /\ T.dir /= "*"
        /\ gamma' = [gamma EXCEPT ![T.id].dir = "*"]
        /\ rule' = "stop"
        /\ UNCHANGED reg
        /\ msg' = [msg EXCEPT ![1] = Append(msg[1],<<T.id,T.pos>>)]


Until(T) == 
    LET
        id == T.id
        order == Head(T.prog)
        nextC == Suiv(T.pos,T.dir,reg.S)
        event == Head(reg.E[id])
    IN
        /\ Len(T.prog) > 0
        /\ reg.G = FALSE
        /\ order[2] = T.dir 
        /\ reg.F[T.pos,T.dir] = "V"
        /\ order[1] = "StartUntil" \*un peu inutile
        /\ nextC /= -1 \*un peu inutile : compare, plus tard, nextC avec Head(order[3]) (jamais -1)
        /\ Head(order[3]) = nextC
        /\ Len(Tail(order[3])) /= 0 \*pas le dernier élément
        /\ gamma' = [gamma EXCEPT 
                            ![id].pos = nextC,
                            ![id].prog[1][3] = Tail(order[3]),
                            ![id].rel = T.rel+1]
        /\ rule' = "until"
        /\ UNCHANGED reg
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
        /\ reg.G = FALSE
        /\ order[2] = T.dir
        /\ reg.F[T.pos,T.dir] = "V"
        /\ order[1] = "StartUntil" \*un peu inutile
        /\ nextC /= -1
        /\ Head(order[3]) = nextC
        /\ Len(Tail(order[3])) = 0 \*dernier élément
        /\ gamma' = [gamma EXCEPT 
                            ![T.id].pos = nextC,
                            ![T.id].prog = Tail(T.prog),
                            ![id].rel = T.rel+1]
        /\ rule' = "until_cons"
        /\ UNCHANGED <<reg,msg>>


        \* Regulateur

StartEvent == \*Simuler une approche grands pas
    LET
        id == Head(msg[1])[1]
        pos == Head(msg[1])[2]
    IN
        /\ reg.G = FALSE
        /\ Len(msg[1]) /= 0
        /\ UNCHANGED gamma
        /\ reg' = [reg EXCEPT !.G = TRUE,
                              !.H[id] = pos] \* actualise la position du train dans l'historique
        /\ rule' = "StartEvent"
        /\ UNCHANGED msg


Turn == \* normalement ok pour lui
    LET
        id == Head(msg[1])[1]
        \*rel == Head(msg[1])[2]
        \*event == reg.E[id][rel] \* Sequence d'ordre de l'event
        event == Head(reg.E[id])
        order == Head(event[2])
        numAig == order[2]
    IN
        /\ reg.G = TRUE
        /\ Len(msg[1]) /= 0
        /\ Len(event[2]) > 0
        /\ order[1] = "turn"
        /\ numAig <= Len(reg.S)
        /\ numAig >= 0
        /\ UNCHANGED gamma
        /\ rule' = "turn" 
        /\ reg' = [reg EXCEPT !.S[numAig] = order[3],
                              !.E[id][1][2] = Tail(event[2])]
        /\ UNCHANGED msg

Att_bf == 
    LET
        id == Head(msg[1])[1]
        \*rel == Head(msg[1])[2]
        \*event == reg.E[id][rel] \* Sequence d'ordre de l'event
        event == Head(reg.E[id])
        order == Head(event[2])
        jet == order[2]
        val == order[3]
    IN 
        /\ reg.G = TRUE
        /\ Len(msg[1]) /= 0
        /\ Len(event[2]) > 0
        /\ order[1] = "att"
        /\ reg.J[jet] /= val
        /\ UNCHANGED gamma
        /\ rule' = "att_bf"
        /\ reg' = [reg EXCEPT !.W[jet,val] = id,
                              !.E[id][1][2] = Tail(event[2])]
        /\ UNCHANGED msg

Att_af == \* TODO: attention à findSection, NextAtt etc...
    LET
        id == Head(msg[1])[1]
        \*rel == Head(msg[1])[2]
        \*event == reg.E[id][rel] \* Sequence d'ordre de l'event
        event == Head(reg.E[id])
        order == Head(event[2])
        jet == order[2]
        val == order[3]
        subseqEv == SubSeq(reg.E[id],2,Len(reg.E[id]))
        target == NextAttTurn(id,subseqEv)
        pos == reg.H[id]
    IN
        /\ reg.G = TRUE
        /\ Len(msg[1]) /= 0
        /\ Len(event[2]) > 0
        /\ order[1] = "att"
        /\ reg.J[jet] = val
        /\ UNCHANGED gamma
        /\ rule' = "att_af" \o ToString(pos) \o ToString(target)
        /\ reg' = [reg EXCEPT !.W[jet,val] = id,
                              !.F[target,"L"] = "R",
                              !.F[target,"R"] = "R",
                              !.F[pos,"L"]    = "V",
                              !.F[pos,"R"]    = "V",
                              !.E[id][1][2] = Tail(event[2])]
        /\ UNCHANGED msg

Incr_bf ==
    LET
        id == Head(msg[1])[1]
        \*rel == Head(msg[1])[2]
        \*event == reg.E[id][rel] \* Sequence d'ordre de l'event
        event == Head(reg.E[id])
        order == Head(event[2])
        jet == order[2]
        val == reg.J[jet]
        id_wait == reg.W[jet,val+1]
    IN
        /\ reg.G = TRUE
        /\ Len(msg[1]) /= 0
        /\ Len(event[2]) > 0
        /\ order[1] = "incr"
        /\ id_wait = -1
        /\ UNCHANGED gamma
        /\ rule' = "incr_bf"
        /\ reg' = [reg EXCEPT !.J[jet] = reg.J[jet]+1,
                              !.E[id][1][2] = Tail(event[2])]
        /\ UNCHANGED msg


Incr_af == \* TODO: attention à findSection, NextAtt etc...
    LET
        id == Head(msg[1])[1]
        \*rel == Head(msg[1])[2]
        \*event == reg.E[id][rel] \* Sequence d'ordre de l'event
        event == Head(reg.E[id])
        order == Head(event[2])
        jet == order[2]
        val == reg.J[jet]
        id_wait == reg.W[jet,val+1]
        subseqEv == SubSeq(reg.E[id_wait],1,Len(reg.E[id_wait]))
        target == NextAttTurn(id_wait,subseqEv)
        pos == reg.H[id_wait]
    IN
        /\ reg.G = TRUE
        /\ Len(msg[1]) /= 0
        /\ Len(event[2]) > 0
        /\ order[1] = "incr"
        /\ id_wait /= -1
        /\ UNCHANGED gamma
        /\ rule' = "incr_af " \o ToString(pos) \o ToString(target)
        /\ reg' = [reg EXCEPT !.J[jet] = reg.J[jet]+1,
                              !.F[target,"L"] = "R",
                              !.F[target,"R"] = "R",
                              !.F[pos,"L"]    = "V",
                              !.F[pos,"R"]    = "V",
                              !.E[id][1][2] = Tail(event[2])]
        /\ UNCHANGED msg


Auth == \* TODO: attention à findSection, NextAtt etc...
    LET
        id == Head(msg[1])[1]
        \*rel == Head(msg[1])[2]
        \*event == reg.E[id][rel] \* Sequence d'ordre de l'event
        event == Head(reg.E[id])
        order == Head(event[2])
        subseqEv == SubSeq(reg.E[id],2,Len(reg.E[id]))
        target == NextAttTurn(id,subseqEv)
        pos == reg.H[id]
    IN
        /\ reg.G = TRUE
        /\ Len(msg[1]) /= 0
        /\ Len(event[2]) > 0
        /\ order[1] = "auth"
        /\ UNCHANGED gamma
        /\ rule' = "auth"
        /\ reg' = [reg EXCEPT !.F[target,"L"] = "R",
                              !.F[target,"R"] = "R",
                              !.F[pos,"L"]    = "V",
                              !.F[pos,"R"]    = "V",
                              !.E[id][1][2] = Tail(event[2])]
        /\ UNCHANGED msg



EndEvent ==
    LET
        id == Head(msg[1])[1]
        \*rel == Head(msg[1])[2]
        \*event == reg.E[id][rel] \* Sequence d'ordre de l'event
        event == Head(reg.E[id])
    IN
        /\ reg.G = TRUE
        /\ Len(msg[1]) /= 0
        /\ Len(event[2]) = 0
        /\ UNCHANGED gamma
        /\ rule' = "EndEvent"
        /\ reg' = [reg EXCEPT !.G = FALSE,
                              !.E[id] = Tail(reg.E[id])]
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

\* Règle de "debug" pour les cas X* -> X[R,L] ? (uniquement pour passer les tests) 
\* Si T.prog vide et que T.pos = pos de l'event 1

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
        \/ IDLE

Spec == Init /\ [][Next]_<<gamma,reg,rule,msg>> /\ WF_<<gamma,reg,rule,msg>>(Next)

=============================================================================
\* Modification History
\* Last modified Mon May 26 13:19:55 CEST 2025 by lucas
\* Created Fri May 09 16:46:37 CEST 2025 by lucas
