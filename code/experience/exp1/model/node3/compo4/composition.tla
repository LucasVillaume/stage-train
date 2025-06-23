----------------------------- MODULE composition -----------------------------

EXTENDS Integers, TLC, Sequences
VARIABLE gamma, reg, sigma, feux, meta, rule

train1 == [
	id |-> 1,
	pos |-> 1,
	dir |-> "*",
	prog |-> <<<<"StartUntil", "L", <<3, 7, 5>>>>>>
]
train2 == [
	id |-> 2,
	pos |-> 6,
	dir |-> "*",
	prog |-> <<<<"StartUntil", "L", <<4>>>>>>
]
train3 == [
	id |-> 3,
	pos |-> 5,
	dir |-> "*",
	prog |-> <<<<"StartUntil", "R", <<7, 3, 2>>>>>>
]


events == <<
    <<<<1, <<<<"att", 3, 1>>>>>>, <<3, <<>>>>, <<7, <<>>>>, <<5, <<>>>>>>,
    <<<<6, <<<<"turn", 5, "v">>, <<"auth">>>>>>, <<4, <<>>>>>>,
    <<<<5, <<>>>>, <<7, <<>>>>, <<3, <<>>>>, <<2, <<<<"turn", 1, "d">>, <<"turn", 2, "v">>, <<"incr", 3>>>>>>>>
>>

token == [x \in 1..8 |-> 0]
wait == [x \in (1..8) \X (0..4) |-> -1]
traffic_lights == [x \in (1..8) \X {"L","R"} |-> "V"]
switch == <<"v", "v", "d", "d", "d">>

Init ==
    /\ gamma = <<train1, train2, train3>>
    /\ reg = [
		E |-> events,
		J |-> token,
		W |-> {}
    	]
    /\ sigma = switch
    /\ feux = [traffic_lights EXCEPT 
			![1,"L"] = "R",
			![1,"R"] = "R",
			![6,"L"] = "R",
			![6,"R"] = "R",
			![2,"L"] = "R",
			![2,"R"] = "R"]
    /\ meta = [
		msg   |-> << <<>>, <<>> >>,
		garde |-> [state |-> "none", requests |-> <<>>]
    	]
    /\ rule = ""

Liveness ==
    /\ <>[] /\ gamma[1].pos = 5
            /\ gamma[1].dir = "*"
    /\ <>[] /\ gamma[2].pos = 4
            /\ gamma[2].dir = "*"
    /\ <>[] /\ gamma[3].pos = 2
            /\ gamma[1].dir = "*"

Safety ==
    /\ [] (gamma[1].pos /= gamma[2].pos /\ gamma[1].pos /= gamma[3].pos /\ gamma[2].pos /= gamma[3].pos)


=============================================================================