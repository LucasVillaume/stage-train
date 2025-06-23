----------------------------- MODULE composition -----------------------------

EXTENDS Integers, TLC, Sequences
VARIABLE gamma, reg, sigma, feux, meta, rule

train1 == [
	id |-> 1,
	pos |-> 5,
	dir |-> "*",
	prog |-> <<<<"StartUntil", "L", <<4>>>>>>
]
train2 == [
	id |-> 2,
	pos |-> 8,
	dir |-> "*",
	prog |-> <<<<"StartUntil", "R", <<3, 2>>>>>>
]
train3 == [
	id |-> 3,
	pos |-> 6,
	dir |-> "*",
	prog |-> <<<<"StartUntil", "L", <<4, 3, 7>>>>>>
]


events == <<
    <<<<5, <<<<"att", 4, 1>>>>>>, <<4, <<>>>>>>,
    <<<<8, <<<<"att", 3, 1>>>>>>, <<3, <<<<"turn", 2, "v">>, <<"turn", 1, "v">>, <<"auth">>>>>>, <<2, <<>>>>>>,
    <<<<6, <<>>>>, <<4, <<>>>>, <<3, <<<<"turn", 5, "d">>, <<"incr", 4>>>>>>, <<7, <<<<"turn", 3, "v">>, <<"incr", 3>>>>>>>>
>>

token == [x \in 1..8 |-> 0]
wait == [x \in (1..8) \X (0..4) |-> -1]
traffic_lights == [x \in (1..8) \X {"L","R"} |-> "V"]
switch == <<"d", "d", "d", "d", "v">>

Init ==
    /\ gamma = <<train1, train2, train3>>
    /\ reg = [
		E |-> events,
		J |-> token,
		W |-> {}
    	]
    /\ sigma = switch
    /\ feux = [traffic_lights EXCEPT 
			![5,"L"] = "R",
			![5,"R"] = "R",
			![8,"L"] = "R",
			![8,"R"] = "R",
			![7,"L"] = "R",
			![7,"R"] = "R"]
    /\ meta = [
		msg   |-> << <<>>, <<>> >>,
		garde |-> [state |-> "none", requests |-> <<>>]
    	]
    /\ rule = ""

Liveness ==
    /\ <>[] /\ gamma[1].pos = 4
            /\ gamma[1].dir = "*"
    /\ <>[] /\ gamma[2].pos = 2
            /\ gamma[2].dir = "*"
    /\ <>[] /\ gamma[3].pos = 7
            /\ gamma[1].dir = "*"

Safety ==
    /\ [] (gamma[1].pos /= gamma[2].pos /\ gamma[1].pos /= gamma[3].pos /\ gamma[2].pos /= gamma[3].pos)


=============================================================================