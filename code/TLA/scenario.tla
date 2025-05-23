------------------------------- MODULE scenario -------------------------------

EXTENDS Integers, TLC, Sequences
VARIABLES gamma, reg, rule


(********************** Collision ***********************)

Init_S3 ==
    LET 
        train1 == [
            id |-> 1,
            pos |-> 9,
            dir |-> "*",
            prog |-> << <<"StartUntil","R",4>> >>
        ]
        train2 == [
            id |-> 2,
            pos |-> 6,
            dir |-> "*",
            prog |-> << <<"StartUntil","L",2>> >>
        ]
        token == <<0,0,0,0>>
        auths == <<4,4>>
        events == <<
                << <<>>, <<<<"turn",1,"d">>>>, <<<<"turn",2,"d">>>>, <<>> >>,
                << <<>>, <<<<"turn",2,"v">>>>, <<<<"turn",1,"v">>>>, <<>> >>
            >>
        nextEv == <<1,1>>
        wait == [x \in (1..4) \X (0..3) |-> -1]
        switch == <<"v", "v">>

    IN
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
    
Suiv_S3(pos, dir, S) ==
    IF      pos = 9 /\ dir = "R"               THEN 1
    ELSE IF pos = 1 /\ dir = "L"               THEN 9
    ELSE IF pos = 1 /\ dir = "R" /\ S[1] = "d" THEN 3
    ELSE IF pos = 2 /\ dir = "R" /\ S[1] = "v" THEN 3
    ELSE IF pos = 3 /\ dir = "R" /\ S[2] = "d" THEN 4
    ELSE IF pos = 3 /\ dir = "R" /\ S[2] = "v" THEN 5
    ELSE IF pos = 3 /\ dir = "L" /\ S[1] = "d" THEN 1
    ELSE IF pos = 3 /\ dir = "L" /\ S[1] = "v" THEN 2
    ELSE IF pos = 4 /\ dir = "L" /\ S[2] = "d" THEN 3
    ELSE IF pos = 5 /\ dir = "L" /\ S[2] = "v" THEN 3
    ELSE IF pos = 5 /\ dir = "R"               THEN 6
    ELSE IF pos = 6 /\ dir = "L"               THEN 5
    ELSE -1


(********************** Maquette ***********************)



Init_S4 == 
    LET 
        train1 == [
            id |-> 1,
            pos |-> 4,
            dir |-> "*",
            prog |-> << <<"StartUntil","L",8>>,<<"StartUntil","R",3>>,<<"StartUntil","L",7>> >>
        ]
        train2 == [
            id |-> 2,
            pos |-> 5,
            dir |-> "*",
            prog |-> << <<"StartUntil","R",4>>, <<"StartUntil","L",3>> >>
        ]
        token == <<0,0,0,0>>
        auths == <<2,1>>
        events == <<
                << <<>>, <<>>, <<<<"turn",3,"d">>,<<"incr",3>>,<<"att",3,2>>>>, <<<<"turn",3,"d">>>>, <<<<"incr",3>>>> >>,
                << <<>>, <<<<"att",3,1>>>>, <<>>, <<<<"turn",3,"v">>,<<"incr",3>>,<<"att",3,3>>>>, <<>> >>
            >>
        nextEv == <<1,1>>
        wait == [x \in (1..4) \X (0..3) |-> -1]
        switch == <<"d", "d", "v", "d", "d">> 

    IN
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


Suiv_S4(pos, dir, S) ==   IF pos = 1 /\ dir = "L" /\ S[1] = "d" /\ S[2] = "v" THEN 3
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



=============================================================================