----------------------------- MODULE composition -----------------------------

EXTENDS Integers, TLC, Sequences
VARIABLE gamma, reg, sigma, feux, meta, rule

train1 == [
	id |-> 1,
	pos |-> 4,
	dir |-> "*",
	prog |-> <<<<"StartUntil", "R", <<6>>>>>>
]
train2 == [
	id |-> 2,
	pos |-> 3,
	dir |-> "*",
	prog |-> <<<<"StartUntil", "L", <<8>>>>>>
]
train3 == [
	id |-> 3,
	pos |-> 5,
	dir |-> "*",
	prog |-> <<<<"StartUntil", "R", <<7>>>>>>
]


events == <<
    <<<<4, <<<<"turn", 5, "v">>, <<"auth">>>>>>, <<6, <<>>>>>>,
    <<<<3, <<<<"turn", 3, "v">>, <<"auth">>>>>>, <<8, <<>>>>>>,
    <<<<5, <<>>>>, <<7, <<>>>>>>
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
			![4,"L"] = "R",
			![4,"R"] = "R",
			![3,"L"] = "R",
			![3,"R"] = "R",
			![7,"L"] = "R",
			![7,"R"] = "R"]
    /\ meta = [
		msg   |-> << <<>>, <<>> >>,
		garde |-> [state |-> "none", requests |-> <<>>]
    	]
    /\ rule = ""

Liveness ==
    /\ <>[] /\ gamma[1].pos = 6
            /\ gamma[1].dir = "*"
    /\ <>[] /\ gamma[2].pos = 8
            /\ gamma[2].dir = "*"
    /\ <>[] /\ gamma[3].pos = 7
            /\ gamma[1].dir = "*"

Safety ==
    /\ [] (gamma[1].pos /= gamma[2].pos /\ gamma[1].pos /= gamma[3].pos /\ gamma[2].pos /= gamma[3].pos)


=============================================================================