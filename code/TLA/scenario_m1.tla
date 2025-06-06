------------------------------- MODULE scenario_m1 -------------------------------

EXTENDS Integers, TLC, Sequences
VARIABLES gamma, reg, rule, msg


(********************** Collision ***********************)

Init_S3 ==
    LET 
        train1 == [
            id |-> 1,
            pos |-> 9,
            dir |-> "*",
            prog |-> << <<"StartUntil","R",4>> >>,
            rel |-> 1
        ]
        train2 == [
            id |-> 2,
            pos |-> 6,
            dir |-> "*",
            prog |-> << <<"StartUntil","L",2>> >>,
            rel |-> 1
        ]
        token == <<0,0,0,0>>
        events == <<
                << <<>>, <<<<"turn",1,"d",1>>,<<"auth">>>>, <<<<"turn",2,"d">>,<<"auth">>>>, <<>> >>,
                << <<>>, <<<<"turn",2,"v",2>>,<<"auth">>>>, <<<<"turn",1,"v">>,<<"auth">>>>, <<>> >>
            >>
        nextEv == <<1,1>>
        wait == [x \in (1..4) \X (0..3) |-> -1]
        switch == <<"v", "v">>
        traffic_lights == [x \in (1..9) \X {"L","R"} |-> "V"]
        historique == [x \in (1..2) |-> -1]
    IN
        /\ gamma = <<train1,train2>>
        /\ reg = [
                E  |-> events,
                J  |-> token,
                S  |-> switch,
                W  |-> wait,
                G  |-> FALSE,
                H  |-> historique,
                F  |-> [traffic_lights EXCEPT ![1,"L"] = "R",
                                              ![1,"R"] = "R",
                                              ![5,"L"] = "R",
                                              ![5,"R"] = "R"]
            ]
        /\ rule = ""
        /\ msg = << <<>>, <<>> >>
    
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
            prog |-> << <<"StartUntil","L",<<3,8>>>>,<<"StartUntil","R",<<3>>>>,<<"StartUntil","L",<<7>>>> >>
        ]
        train2 == [
            id |-> 2,
            pos |-> 5,
            dir |-> "*",
            prog |-> << <<"StartUntil","R",<<7,3,4>>>>, <<"StartUntil","L",<<3>>>> >>
        ]
        token == <<0,0,0,0>>
        events == <<
                << <<4,<<>>>>, <<3,<<>>>>, <<8,<<<<"turn",3,"d">>,<<"incr",3>>,<<"att",3,2>>>>>>, <<3,<<<<"turn",3,"d">>,<<"auth">>>>>>, <<7,<<<<"incr",3>>>>>> >>,
                << <<5,<<>>>>, <<7,<<<<"att",3,1>>>>>>, <<3,<<>>>>, <<4,<<<<"turn",3,"v">>,<<"incr",3>>,<<"att",3,3>>>>>>, <<3,<<>>>> >>
            >>
        nextEv == <<1,1>>
        wait == [x \in (1..4) \X (0..3) |-> -1]
        switch == <<"d", "d", "v", "d", "d">> 
        historique == [x \in (1..2) |-> -1]
        traffic_lights == [x \in (1..8) \X {"L","R"} |-> "V"]
    IN
        /\ gamma = <<train1,train2>>
        /\ reg = [
                E  |-> events,
                J  |-> token,
                S  |-> switch,
                W  |-> wait,
                G  |-> FALSE,
                H  |-> historique,
                F  |-> [traffic_lights EXCEPT ![7,"L"] = "R",
                                              ![7,"R"] = "R",
                                              ![8,"R"] = "R",
                                              ![8,"L"] = "R"]
            ]
        /\ rule = ""
        /\ msg = << <<>>, <<>> >>


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


(********************** Défaut 1 ***********************)


Init_D1 ==
    LET 
        train1 == [
            id |-> 1,
            pos |-> 1,
            dir |-> "*",
            prog |-> << <<"StartUntil","R",<<2,4>>>>,<<"StartUntil","L",<<3,1>>>> >>,
            rel |-> 1
        ]
        train2 == [
            id |-> 2,
            pos |-> 4,
            dir |-> "*",
            prog |-> << <<"StartUntil","L",<<3,1>>>>, <<"StartUntil","R",<<2,4>>>> >>,
            rel |-> 1
        ]
        token == <<0,0,0,0>>
        events == <<
                << <<1,<<>>>>, <<2,<<<<"turn",1,"v">>,<<"incr",1>>,<<"att",4,1>>>>>>, <<4,<<<<"turn",2,"d">>,<<"incr",2>>,<<"att",3,1>>>>>>, <<3,<<<<"turn",2,"v">>,<<"incr",4>>,<<"att",1,2>>>>>>, <<1,<<>>>> >>,
                << <<4,<<>>>>, <<3,<<<<"turn",2,"v">>,<<"incr",4>>,<<"att",1,1>>>>>>, <<1,<<<<"turn",1,"d">>,<<"incr",3>>,<<"att",2,1>>>>>>, <<2,<<<<"turn",1,"v">>,<<"incr",1>>,<<"att",4,2>>>>>>, <<4,<<>>>> >>
            >>
        nextEv == <<1,1>>
        wait == [x \in (1..4) \X (0..3) |-> -1]
        switch == <<"d", "d">> 
        historique == [x \in (1..2) |-> -1]
        traffic_lights == [x \in (1..4) \X {"L","R"} |-> "V"]
    IN
        /\ gamma = <<train1,train2>>
        /\ reg = [
                E  |-> events,
                J  |-> token,
                S  |-> switch,
                W  |-> wait,
                G  |-> FALSE,
                H  |-> historique,
                F  |-> [traffic_lights EXCEPT ![2,"L"] = "R",
                                              ![2,"R"] = "R",
                                              ![3,"R"] = "R",
                                              ![3,"L"] = "R"]
            ]
        /\ rule = ""
        /\ msg = << <<>>, <<>> >>

Suiv_D1(pos, dir, S) ==   IF pos = 1 /\ dir = "R" /\ S[1] = "d" THEN 2
                     ELSE IF pos = 1 /\ dir = "R" /\ S[1] = "v" THEN 3
                     ELSE IF pos = 2 /\ dir = "R" /\ S[2] = "v" THEN 4
                     ELSE IF pos = 2 /\ dir = "L" /\ S[1] = "d" THEN 1
                     ELSE IF pos = 3 /\ dir = "R" /\ S[2] = "d" THEN 4
                     ELSE IF pos = 3 /\ dir = "L" /\ S[1] = "v" THEN 1
                     ELSE IF pos = 4 /\ dir = "L" /\ S[2] = "d" THEN 3
                     ELSE IF pos = 4 /\ dir = "L" /\ S[2] = "v" THEN 2
                     ELSE -1


(********************** Défaut 2 ***********************)


Init_D2 ==
    LET 
        train1 == [
            id |-> 1,
            pos |-> 1,
            dir |-> "*",
            prog |-> << <<"StartUntil","R",<<2>>>>, <<"StartUntil","L",<<3>>>>, <<"StartUntil","R",<<1>>>> >>,
            rel |-> 1
        ]
        train2 == [
            id |-> 2,
            pos |-> 3,
            dir |-> "*",
            prog |-> << <<"StartUntil","L",<<1>>>>, <<"StartUntil","R",<<2>>>>, <<"StartUntil","L",<<3>>>> >>,
            rel |-> 1
        ]
        token == <<0,0,0,0>>
        events == <<
                << <<1,<<>>>>, <<2,<<<<"turn",1,"-">>,<<"incr",1>>,<<"att",3,1>>>>>>, <<3,<<<<"turn",1,"d">>,<<"incr",2>>,<<"att",1,2>>>>>>, <<1,<<<<"turn",1,"v">>,<<"incr",3>>>>>> >>,
                << <<3,<<<<"att",1,1>>>>>>, <<1,<<<<"turn",1,"v">>,<<"incr",3>>,<<"att",2,1>>>>>>, <<2,<<<<"turn",1,"-">>,<<"incr",1>>,<<"att",3,2>>>>>>, <<3,<<>>>> >>
            >>
        nextEv == <<1,1>>
        wait == [x \in (1..4) \X (0..3) |-> -1]
        switch == <<"d">> 
        historique == [x \in (1..2) |-> -1]
        traffic_lights == [x \in (1..4) \X {"L","R"} |-> "V"]
    IN
        /\ gamma = <<train1,train2>>
        /\ reg = [
                E  |-> events,
                J  |-> token,
                S  |-> switch,
                W  |-> wait,
                G  |-> FALSE,
                H  |-> historique,
                F  |-> [traffic_lights EXCEPT ![2,"L"] = "R",
                                              ![2,"R"] = "R",
                                              ![3,"R"] = "R",
                                              ![3,"L"] = "R"]
            ]
        /\ rule = ""
        /\ msg = << <<>>, <<>> >>

Suiv_D2(pos, dir, S) ==   IF pos = 1 /\ dir = "R" /\ S[1] = "-" THEN 3
                     ELSE IF pos = 1 /\ dir = "R" /\ S[1] = "d" THEN 2
                     ELSE IF pos = 1 /\ dir = "L" /\ S[1] = "-" THEN 3
                     ELSE IF pos = 1 /\ dir = "L" /\ S[1] = "d" THEN 2
                     
                     ELSE IF pos = 2 /\ dir = "R" /\ S[1] = "d" THEN 1
                     ELSE IF pos = 2 /\ dir = "R" /\ S[1] = "v" THEN 3
                     ELSE IF pos = 2 /\ dir = "L" /\ S[1] = "d" THEN 1
                     ELSE IF pos = 2 /\ dir = "L" /\ S[1] = "v" THEN 3
                     
                     ELSE IF pos = 3 /\ dir = "L" /\ S[1] = "v" THEN 2
                     ELSE IF pos = 3 /\ dir = "L" /\ S[1] = "-" THEN 1
                     ELSE IF pos = 3 /\ dir = "R" /\ S[1] = "v" THEN 2
                     ELSE IF pos = 3 /\ dir = "R" /\ S[1] = "-" THEN 1
                     ELSE -1


(********************** Trois trains ***********************)


Init_S8 ==
    LET 
        train1 == [
            id |-> 1,
            pos |-> 1,
            dir |-> "*",
            prog |-> << <<"StartUntil","R",5>> >>,
            rel |-> 1
        ]
        train2 == [
            id |-> 2,
            pos |-> 2,
            dir |-> "*",
            prog |-> << <<"StartUntil","R",4>> >>,
            rel |-> 1
        ]
        train3 == [
            id |-> 3,
            pos |-> 4,
            dir |-> "*",
            prog |-> << <<"StartUntil","L",1>> >>,
            rel |-> 1
        ]
        token == <<0,0,0,0,0>>
        events == <<
                << <<>>, <<>>, <<<<"turn",2,"d">>,<<"incr",3>> >>>>,
                << <<<<"att",3,2>>>>, <<>>, <<>>>>,
                << <<<<"att",3,1>>>>, <<>>, <<<<"turn",1,"v">>,<<"incr",3>>>> >>
            >>
        nextEv == <<1,1,1>>
        wait == [x \in (1..4) \X (0..3) |-> -1]
        switch == <<"d", "v">>
        traffic_lights == [x \in (1..5) \X {"L","R"} |-> "V"]
    IN
        /\ gamma = <<train1,train2,train3>>
        /\ reg = [
                E  |-> events,
                J  |-> token,
                S  |-> switch,
                W  |-> wait,
                G  |-> FALSE,
                F  |-> [traffic_lights EXCEPT ![2,"L"] = "R",
                                              ![2,"R"] = "R",
                                              ![4,"L"] = "R",
                                              ![4,"R"] = "R",
                                              ![5,"L"] = "R",
                                              ![5,"R"] = "R"]
            ]
        /\ rule = ""
        /\ msg = << <<>>, <<>> >>
    
Suiv_S8(pos, dir, S) ==
    IF      pos = 1 /\ dir = "R" /\ S[1] = "d" THEN 3
    ELSE IF pos = 2 /\ dir = "R" /\ S[1] = "v" THEN 3
    ELSE IF pos = 3 /\ dir = "L" /\ S[1] = "d" THEN 1
    ELSE IF pos = 3 /\ dir = "L" /\ S[1] = "v" THEN 2
    ELSE IF pos = 3 /\ dir = "R" /\ S[2] = "d" THEN 4
    ELSE IF pos = 3 /\ dir = "R" /\ S[2] = "v" THEN 5
    ELSE IF pos = 4 /\ dir = "L" /\ S[2] = "d" THEN 3
    ELSE IF pos = 5 /\ dir = "L" /\ S[2] = "v" THEN 3
    ELSE -1


(********************** Maquette Composition ***********************)


Init_S4_1 == 
    LET 
        train1 == [
            id |-> 1,
            pos |-> 4,
            dir |-> "*",
            prog |-> << <<"StartUntil","L",8>>>>,
            rel |-> 1
        ]
        train2 == [
            id |-> 2,
            pos |-> 5,
            dir |-> "*",
            prog |-> << <<"StartUntil","R",3>>>>,
            rel |-> 1
        ]
        token == <<0,0,0,0>>
        events == <<
                << <<>>, <<>>, <<<<"turn",3,"d">>,<<"incr",3>>>> >>,
                << <<>>, <<<<"att",3,1>>>>, <<>> >>
            >>
        nextEv == <<1,1>>
        wait == [x \in (1..4) \X (0..3) |-> -1]
        switch == <<"d", "d", "v", "d", "d">> 
        traffic_lights == [x \in (1..8) \X {"L","R"} |-> "V"]
    IN
        /\ gamma = <<train1,train2>>
        /\ reg = [
                E  |-> events,
                J  |-> token,
                S  |-> switch,
                W  |-> wait,
                G  |-> FALSE,
                F  |-> [traffic_lights EXCEPT ![7,"L"] = "R",
                                              ![7,"R"] = "R",
                                              ![8,"R"] = "R",
                                              ![8,"L"] = "R"]
            ]
        /\ rule = ""
        /\ msg = << <<>>, <<>> >>


Init_S4_2 == 
    LET 
        train1 == [
            id |-> 1,
            pos |-> 8,
            dir |-> "*",
            prog |-> <<<<"StartUntil","R",3>>,<<"StartUntil","L",7>> >>,
            rel |-> 1
        ]
        train2 == [
            id |-> 2,
            pos |-> 3,
            dir |-> "*",
            prog |-> << <<"StartUntil","R",4>>, <<"StartUntil","L",3>> >>,
            rel |-> 1
        ]
        token == <<0,0,0,0>>
        events == <<
                << <<<<"att",3,1>>>>, <<<<"turn",3,"d">>,<<"auth">>>>, <<<<"incr",3>>>> >>,
                << <<>>, <<<<"turn",3,"v">>,<<"incr",3>>,<<"att",3,2>>>>, <<>> >>
            >>
        nextEv == <<1,1>>
        wait == [x \in (1..4) \X (0..3) |-> -1]
        switch == <<"d", "d", "d", "d", "d">> 
        traffic_lights == [x \in (1..8) \X {"L","R"} |-> "V"]
    IN
        /\ gamma = <<train1,train2>>
        /\ reg = [
                E  |-> events,
                J  |-> token,
                S  |-> switch,
                W  |-> wait,
                G  |-> FALSE,
                F  |-> [traffic_lights EXCEPT ![4,"L"] = "R",
                                              ![4,"R"] = "R",
                                              ![8,"R"] = "R",
                                              ![8,"L"] = "R"]
            ]
        /\ rule = ""
        /\ msg = << <<>>, <<>> >>




=============================================================================