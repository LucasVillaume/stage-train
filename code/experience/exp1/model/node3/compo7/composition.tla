----------------------------- MODULE composition -----------------------------

EXTENDS Integers, TLC, Sequences
VARIABLE gamma, reg, sigma, feux, meta, rule

train1 == [
	id |-> 1,
	pos |-> 2,
	dir |-> "*",
	prog |-> <<<<"StartUntil", "L", <<3, 7, 6, 4>>>>>>
]
train2 == [
	id |-> 2,
	pos |-> 6,
	dir |-> "*",
	prog |-> <<<<"StartUntil", "R", <<7, 3, 4, 5>>>>>>
]
train3 == [
	id |-> 3,
	pos |-> 1,
	dir |-> "*",
	prog |-> <<>>
]


events == <<
    <<<<2, <<<<"att", 3, 1>>>>>>, <<3, <<>>>>, <<7, <<>>>>, <<6, <<<<"att", 4, 1>>>>>>, <<4, <<>>>>>>,
    <<<<6, <<>>>>, <<7, <<>>>>, <<3, <<>>>>, <<4, <<<<"turn", 1, "v">>, <<"turn", 2, "v">>, <<"incr", 3>>>>>>, <<5, <<<<"turn", 5, "v">>, <<"incr", 4>>>>>>>>,
    <<<<1, <<>>>>>>
>>

token == [x \in 1..8 |-> 0]
wait == [x \in (1..8) \X (0..4) |-> -1]
traffic_lights == [x \in (1..8) \X {"L","R"} |-> "V"]
switch == <<"d", "d", "d", "v", "d">>

Init ==
    /\ gamma = <<train1, train2, train3>>
    /\ reg = [
		E |-> events,
		J |-> token,
		W |-> {}
    	]
    /\ sigma = switch
    /\ feux = [traffic_lights EXCEPT 
			![2,"L"] = "R",
			![2,"R"] = "R",
			![5,"L"] = "R",
			![5,"R"] = "R",
			![1,"L"] = "R",
			![1,"R"] = "R"]
    /\ meta = [
		msg   |-> << <<>>, <<>> >>,
		garde |-> [state |-> "none", requests |-> <<>>]
    	]
    /\ rule = ""

Liveness ==
    /\ <>[] /\ gamma[1].pos = 4
            /\ gamma[1].dir = "*"
    /\ <>[] /\ gamma[2].pos = 5
            /\ gamma[2].dir = "*"
    /\ <>[] /\ gamma[3].pos = 1
            /\ gamma[1].dir = "*"

Safety ==
    /\ [] (gamma[1].pos /= gamma[2].pos /\ gamma[1].pos /= gamma[3].pos /\ gamma[2].pos /= gamma[3].pos)


=============================================================================