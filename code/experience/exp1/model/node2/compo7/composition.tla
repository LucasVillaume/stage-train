----------------------------- MODULE composition -----------------------------

EXTENDS Integers, TLC, Sequences
VARIABLE gamma, reg, sigma, feux, meta, rule

train1 == [
	id |-> 1,
	pos |-> 8,
	dir |-> "*",
	prog |-> <<<<"StartUntil", "R", <<3, 2>>>>>>
]
train2 == [
	id |-> 2,
	pos |-> 1,
	dir |-> "*",
	prog |-> <<>>
]
train3 == [
	id |-> 3,
	pos |-> 7,
	dir |-> "*",
	prog |-> <<<<"StartUntil", "L", <<5, 4>>>>>>
]


events == <<
    <<<<8, <<<<"turn", 3, "v">>, <<"auth">>>>>>, <<3, <<<<"turn", 2, "v">>, <<"turn", 1, "v">>, <<"auth">>>>>>, <<2, <<>>>>>>,
    <<<<1, <<>>>>>>,
    <<<<7, <<>>>>, <<5, <<>>>>, <<4, <<>>>>>>
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
			![8,"L"] = "R",
			![8,"R"] = "R",
			![1,"L"] = "R",
			![1,"R"] = "R",
			![4,"L"] = "R",
			![4,"R"] = "R"]
    /\ meta = [
		msg   |-> << <<>>, <<>> >>,
		garde |-> [state |-> "none", requests |-> <<>>]
    	]
    /\ rule = ""

Liveness ==
    /\ <>[] /\ gamma[1].pos = 2
            /\ gamma[1].dir = "*"
    /\ <>[] /\ gamma[2].pos = 1
            /\ gamma[2].dir = "*"
    /\ <>[] /\ gamma[3].pos = 4
            /\ gamma[1].dir = "*"

Safety ==
    /\ [] (gamma[1].pos /= gamma[2].pos /\ gamma[1].pos /= gamma[3].pos /\ gamma[2].pos /= gamma[3].pos)


=============================================================================