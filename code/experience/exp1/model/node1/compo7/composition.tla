----------------------------- MODULE composition -----------------------------

EXTENDS Integers, TLC, Sequences
VARIABLE gamma, reg, sigma, feux, meta, rule

train1 == [
	id |-> 1,
	pos |-> 4,
	dir |-> "*",
	prog |-> <<<<"StartUntil", "R", <<6, 7>>>>>>
]
train2 == [
	id |-> 2,
	pos |-> 7,
	dir |-> "*",
	prog |-> <<<<"StartUntil", "L", <<5, 4>>>>>>
]
train3 == [
	id |-> 3,
	pos |-> 1,
	dir |-> "*",
	prog |-> <<<<"StartUntil", "L", <<3, 8>>>>>>
]


events == <<
    <<<<4, <<>>>>, <<6, <<<<"turn", 5, "d">>, <<"incr", 4>>, <<"att", 7, 1>>>>>>, <<7, <<>>>>>>,
    <<<<7, <<>>>>, <<5, <<<<"turn", 4, "v">>, <<"incr", 7>>, <<"att", 4, 1>>>>>>, <<4, <<>>>>>>,
    <<<<1, <<<<"turn", 1, "d">>, <<"turn", 2, "v">>, <<"auth">>>>>>, <<3, <<<<"turn", 3, "v">>, <<"auth">>>>>>, <<8, <<>>>>>>
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
			![6,"L"] = "R",
			![6,"R"] = "R",
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
    /\ <>[] /\ gamma[1].pos = 7
            /\ gamma[1].dir = "*"
    /\ <>[] /\ gamma[2].pos = 4
            /\ gamma[2].dir = "*"
    /\ <>[] /\ gamma[3].pos = 8
            /\ gamma[1].dir = "*"

Safety ==
    /\ [] (gamma[1].pos /= gamma[2].pos /\ gamma[1].pos /= gamma[3].pos /\ gamma[2].pos /= gamma[3].pos)


=============================================================================