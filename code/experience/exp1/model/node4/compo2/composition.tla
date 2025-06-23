----------------------------- MODULE composition -----------------------------

EXTENDS Integers, TLC, Sequences
VARIABLE gamma, reg, sigma, feux, meta, rule

train1 == [
	id |-> 1,
	pos |-> 7,
	dir |-> "*",
	prog |-> <<<<"StartUntil", "L", <<5, 4, 3>>>>>>
]
train2 == [
	id |-> 2,
	pos |-> 4,
	dir |-> "*",
	prog |-> <<<<"StartUntil", "L", <<3, 8>>>>>>
]
train3 == [
	id |-> 3,
	pos |-> 1,
	dir |-> "*",
	prog |-> <<>>
]


events == <<
    <<<<7, <<<<"turn", 4, "d">>, <<"auth">>>>>>, <<5, <<<<"att", 4, 1>>>>>>, <<4, <<<<"att", 3, 1>>>>>>, <<3, <<>>>>>>,
    <<<<4, <<>>>>, <<3, <<<<"turn", 5, "d">>, <<"incr", 4>>>>>>, <<8, <<<<"incr", 3>>>>>>>>,
    <<<<1, <<>>>>>>
>>

token == [x \in 1..8 |-> 0]
wait == [x \in (1..8) \X (0..4) |-> -1]
traffic_lights == [x \in (1..8) \X {"L","R"} |-> "V"]
switch == <<"d", "d", "v", "d", "d">>

Init ==
    /\ gamma = <<train1, train2, train3>>
    /\ reg = [
		E |-> events,
		J |-> token,
		W |-> {}
    	]
    /\ sigma = switch
    /\ feux = [traffic_lights EXCEPT 
			![7,"L"] = "R",
			![7,"R"] = "R",
			![8,"L"] = "R",
			![8,"R"] = "R",
			![1,"L"] = "R",
			![1,"R"] = "R"]
    /\ meta = [
		msg   |-> << <<>>, <<>> >>,
		garde |-> [state |-> "none", requests |-> <<>>]
    	]
    /\ rule = ""

Liveness ==
    /\ <>[] /\ gamma[1].pos = 3
            /\ gamma[1].dir = "*"
    /\ <>[] /\ gamma[2].pos = 8
            /\ gamma[2].dir = "*"
    /\ <>[] /\ gamma[3].pos = 1
            /\ gamma[1].dir = "*"

Safety ==
    /\ [] (gamma[1].pos /= gamma[2].pos /\ gamma[1].pos /= gamma[3].pos /\ gamma[2].pos /= gamma[3].pos)


=============================================================================