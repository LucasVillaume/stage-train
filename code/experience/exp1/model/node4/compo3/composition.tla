----------------------------- MODULE composition -----------------------------

EXTENDS Integers, TLC, Sequences
VARIABLE gamma, reg, sigma, feux, meta, rule

train1 == [
	id |-> 1,
	pos |-> 6,
	dir |-> "*",
	prog |-> <<>>
]
train2 == [
	id |-> 2,
	pos |-> 5,
	dir |-> "*",
	prog |-> <<>>
]
train3 == [
	id |-> 3,
	pos |-> 4,
	dir |-> "*",
	prog |-> <<<<"StartUntil", "L", <<3, 8>>>>>>
]


events == <<
    <<<<6, <<>>>>>>,
    <<<<5, <<>>>>>>,
    <<<<4, <<>>>>, <<3, <<>>>>, <<8, <<>>>>>>
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
			![6,"L"] = "R",
			![6,"R"] = "R",
			![5,"L"] = "R",
			![5,"R"] = "R",
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
    /\ <>[] /\ gamma[2].pos = 5
            /\ gamma[2].dir = "*"
    /\ <>[] /\ gamma[3].pos = 8
            /\ gamma[1].dir = "*"

Safety ==
    /\ [] (gamma[1].pos /= gamma[2].pos /\ gamma[1].pos /= gamma[3].pos /\ gamma[2].pos /= gamma[3].pos)


=============================================================================