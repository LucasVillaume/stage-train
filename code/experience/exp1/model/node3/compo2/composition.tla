----------------------------- MODULE composition -----------------------------

EXTENDS Integers, TLC, Sequences
VARIABLE gamma, reg, sigma, feux, meta, rule

train1 == [
	id |-> 1,
	pos |-> 4,
	dir |-> "*",
	prog |-> <<<<"StartUntil", "L", <<3, 7, 5>>>>>>
]
train2 == [
	id |-> 2,
	pos |-> 8,
	dir |-> "*",
	prog |-> <<>>
]
train3 == [
	id |-> 3,
	pos |-> 6,
	dir |-> "*",
	prog |-> <<>>
]


events == <<
    <<<<4, <<<<"turn", 2, "d">>, <<"auth">>>>>>, <<3, <<<<"turn", 3, "d">>, <<"auth">>>>>>, <<7, <<<<"turn", 4, "d">>, <<"auth">>>>>>, <<5, <<>>>>>>,
    <<<<8, <<>>>>>>,
    <<<<6, <<>>>>>>
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
			![8,"L"] = "R",
			![8,"R"] = "R",
			![6,"L"] = "R",
			![6,"R"] = "R"]
    /\ meta = [
		msg   |-> << <<>>, <<>> >>,
		garde |-> [state |-> "none", requests |-> <<>>]
    	]
    /\ rule = ""

Liveness ==
    /\ <>[] /\ gamma[1].pos = 5
            /\ gamma[1].dir = "*"
    /\ <>[] /\ gamma[2].pos = 8
            /\ gamma[2].dir = "*"
    /\ <>[] /\ gamma[3].pos = 6
            /\ gamma[1].dir = "*"

Safety ==
    /\ [] (gamma[1].pos /= gamma[2].pos /\ gamma[1].pos /= gamma[3].pos /\ gamma[2].pos /= gamma[3].pos)


=============================================================================