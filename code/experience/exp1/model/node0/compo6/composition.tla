----------------------------- MODULE composition -----------------------------

EXTENDS Integers, TLC, Sequences
VARIABLE gamma, reg, sigma, feux, meta, rule

train1 == [
	id |-> 1,
	pos |-> 6,
	dir |-> "*",
	prog |-> <<<<"StartUntil", "L", <<4, 3>>>>>>
]
train2 == [
	id |-> 2,
	pos |-> 5,
	dir |-> "*",
	prog |-> <<<<"StartUntil", "L", <<4, 3, 7>>>>>>
]
train3 == [
	id |-> 3,
	pos |-> 8,
	dir |-> "*",
	prog |-> <<>>
]


events == <<
    <<<<6, <<<<"att", 4, 1>>>>>>, <<4, <<<<"att", 3, 1>>>>>>, <<3, <<>>>>>>,
    <<<<5, <<>>>>, <<4, <<>>>>, <<3, <<<<"turn", 5, "v">>, <<"incr", 4>>>>>>, <<7, <<<<"incr", 3>>>>>>>>,
    <<<<8, <<>>>>>>
>>

token == [x \in 1..8 |-> 0]
wait == [x \in (1..8) \X (0..4) |-> -1]
traffic_lights == [x \in (1..8) \X {"L","R"} |-> "V"]
switch == <<"d", "d", "d", "d", "d">>

Init ==
    /\ gamma = <<train1, train2, train3>>
    /\ reg = [
		E |-> events,
		J |-> token,
		W |-> {}
    	]
    /\ sigma = switch
    /\ feux = [traffic_lights EXCEPT 
			![6,"L"] = "R",
			![6,"R"] = "R",
			![7,"L"] = "R",
			![7,"R"] = "R",
			![8,"L"] = "R",
			![8,"R"] = "R"]
    /\ meta = [
		msg   |-> << <<>>, <<>> >>,
		garde |-> [state |-> "none", requests |-> <<>>]
    	]
    /\ rule = ""

Liveness ==
    /\ <>[] /\ gamma[1].pos = 3
            /\ gamma[1].dir = "*"
    /\ <>[] /\ gamma[2].pos = 7
            /\ gamma[2].dir = "*"
    /\ <>[] /\ gamma[3].pos = 8
            /\ gamma[1].dir = "*"

Safety ==
    /\ [] (gamma[1].pos /= gamma[2].pos /\ gamma[1].pos /= gamma[3].pos /\ gamma[2].pos /= gamma[3].pos)


=============================================================================