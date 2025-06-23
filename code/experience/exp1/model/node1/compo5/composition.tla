----------------------------- MODULE composition -----------------------------

EXTENDS Integers, TLC, Sequences
VARIABLE gamma, reg, sigma, feux, meta, rule

train1 == [
	id |-> 1,
	pos |-> 7,
	dir |-> "*",
	prog |-> <<<<"StartUntil", "L", <<5, 4, 3, 8>>>>>>
]
train2 == [
	id |-> 2,
	pos |-> 2,
	dir |-> "*",
	prog |-> <<>>
]
train3 == [
	id |-> 3,
	pos |-> 1,
	dir |-> "*",
	prog |-> <<>>
]


events == <<
    <<<<7, <<>>>>, <<5, <<>>>>, <<4, <<>>>>, <<3, <<>>>>, <<8, <<>>>>>>,
    <<<<2, <<>>>>>>,
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
			![8,"L"] = "R",
			![8,"R"] = "R",
			![2,"L"] = "R",
			![2,"R"] = "R",
			![1,"L"] = "R",
			![1,"R"] = "R"]
    /\ meta = [
		msg   |-> << <<>>, <<>> >>,
		garde |-> [state |-> "none", requests |-> <<>>]
    	]
    /\ rule = ""

Liveness ==
    /\ <>[] /\ gamma[1].pos = 8
            /\ gamma[1].dir = "*"
    /\ <>[] /\ gamma[2].pos = 2
            /\ gamma[2].dir = "*"
    /\ <>[] /\ gamma[3].pos = 1
            /\ gamma[1].dir = "*"

Safety ==
    /\ [] (gamma[1].pos /= gamma[2].pos /\ gamma[1].pos /= gamma[3].pos /\ gamma[2].pos /= gamma[3].pos)


=============================================================================