----------------------------- MODULE composition -----------------------------

EXTENDS Integers, TLC, Sequences
VARIABLE gamma, reg, sigma, feux, meta, rule

train1 == [
	id |-> 1,
	pos |-> 2,
	dir |-> "*",
	prog |-> <<<<"StartUntil", "L", <<3, 8>>>>>>
]
train2 == [
	id |-> 2,
	pos |-> 7,
	dir |-> "*",
	prog |-> <<<<"StartUntil", "L", <<6>>>>>>
]
train3 == [
	id |-> 3,
	pos |-> 4,
	dir |-> "*",
	prog |-> <<<<"StartUntil", "R", <<5>>>>>>
]


events == <<
    <<<<2, <<<<"turn", 1, "v">>, <<"turn", 2, "v">>, <<"auth">>>>>>, <<3, <<<<"turn", 3, "v">>, <<"auth">>>>>>, <<8, <<>>>>>>,
    <<<<7, <<<<"turn", 4, "v">>, <<"auth">>>>>>, <<6, <<>>>>>>,
    <<<<4, <<<<"turn", 5, "d">>, <<"auth">>>>>>, <<5, <<>>>>>>
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
			![2,"L"] = "R",
			![2,"R"] = "R",
			![7,"L"] = "R",
			![7,"R"] = "R",
			![4,"L"] = "R",
			![4,"R"] = "R"]
    /\ meta = [
		msg   |-> << <<>>, <<>> >>,
		garde |-> [state |-> "none", requests |-> <<>>]
    	]
    /\ rule = ""

Liveness ==
    /\ <>[] /\ gamma[1].pos = 8
            /\ gamma[1].dir = "*"
    /\ <>[] /\ gamma[2].pos = 6
            /\ gamma[2].dir = "*"
    /\ <>[] /\ gamma[3].pos = 5
            /\ gamma[1].dir = "*"

Safety ==
    /\ [] (gamma[1].pos /= gamma[2].pos /\ gamma[1].pos /= gamma[3].pos /\ gamma[2].pos /= gamma[3].pos)


=============================================================================