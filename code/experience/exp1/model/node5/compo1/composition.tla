----------------------------- MODULE composition -----------------------------

EXTENDS Integers, TLC, Sequences
VARIABLE gamma, reg, sigma, feux, meta, rule

train1 == [
	id |-> 1,
	pos |-> 4,
	dir |-> "*",
	prog |-> <<<<"StartUntil", "L", <<3, 7, 6>>>>>>
]
train2 == [
	id |-> 2,
	pos |-> 1,
	dir |-> "*",
	prog |-> <<<<"StartUntil", "L", <<3, 7, 5, 4>>>>>>
]
train3 == [
	id |-> 3,
	pos |-> 8,
	dir |-> "*",
	prog |-> <<>>
]


events == <<
    <<<<4, <<>>>>, <<3, <<>>>>, <<7, <<<<"turn", 1, "d">>, <<"turn", 2, "v">>, <<"incr", 3>>>>>>, <<6, <<<<"incr", 7>>>>>>>>,
    <<<<1, <<<<"att", 3, 1>>>>>>, <<3, <<<<"att", 7, 1>>>>>>, <<7, <<<<"turn", 4, "d">>, <<"auth">>>>>>, <<5, <<<<"turn", 5, "d">>, <<"auth">>>>>>, <<4, <<>>>>>>,
    <<<<8, <<>>>>>>
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
			![6,"L"] = "R",
			![6,"R"] = "R",
			![1,"L"] = "R",
			![1,"R"] = "R",
			![8,"L"] = "R",
			![8,"R"] = "R"]
    /\ meta = [
		msg   |-> << <<>>, <<>> >>,
		garde |-> [state |-> "none", requests |-> <<>>]
    	]
    /\ rule = ""

Liveness ==
    /\ <>[] /\ gamma[1].pos = 6
            /\ gamma[1].dir = "*"
    /\ <>[] /\ gamma[2].pos = 4
            /\ gamma[2].dir = "*"
    /\ <>[] /\ gamma[3].pos = 8
            /\ gamma[1].dir = "*"

Safety ==
    /\ [] (gamma[1].pos /= gamma[2].pos /\ gamma[1].pos /= gamma[3].pos /\ gamma[2].pos /= gamma[3].pos)


=============================================================================