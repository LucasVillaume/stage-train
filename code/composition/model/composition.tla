----------------------------- MODULE composition -----------------------------

EXTENDS Integers, TLC, Sequences
VARIABLE gamma, reg, rule, msg

train1 == [
	id |-> 1,
	pos |-> 7,
	dir |-> "*",
	prog |-> <<>>,
	rel |-> 1
]
train2 == [
	id |-> 2,
	pos |-> 3,
	dir |-> "*",
	prog |-> <<<<"StartUntil", "L", <<8>>>>>>,
	rel |-> 1
]
train3 == [
	id |-> 3,
	pos |-> 2,
	dir |-> "*",
	prog |-> <<>>,
	rel |-> 1
]


events == <<
    <<<<7, <<>>>>>>,
    <<<<3, <<<<"turn", 3, "v">>>>>>, <<8, <<>>>>>>,
    <<<<2, <<>>>>>>
>>

token == [x \in 1..8 |-> 0]
wait == [x \in (1..8) \X (0..4) |-> -1]
historique == [x \in 1..3 |-> -1]
traffic_lights == [x \in (1..8) \X {"L","R"} |-> "V"]
switch == <<"d", "d", "d", "d", "d">>

Init ==
    /\ gamma = <<train1, train2, train3>>
    /\ reg = [
		E |-> events,
		J |-> token,
		S |-> switch,
		W |-> wait,
		G |-> FALSE,
		H |-> historique,
		F |-> [traffic_lights EXCEPT 
			![7,"L"] = "R",
			![7,"R"] = "R",
			![8,"L"] = "R",
			![8,"R"] = "R",
			![2,"L"] = "R",
			![2,"R"] = "R"]
    	]
    /\ rule = ""
    /\ msg = << <<>>, <<>> >>

Liveness ==
    /\ <>[] /\ gamma[1].pos = 7
             /\ gamma[1].dir = "*"
    /\ <>[] /\ gamma[2].pos = 8
             /\ gamma[2].dir = "*"
    /\ <>[] /\ gamma[3].pos = 2
             /\ gamma[1].dir = "*"

Safety ==
    /\ [] (gamma[1].pos /= gamma[2].pos /\ gamma[1].pos /= gamma[3].pos /\ gamma[2].pos /= gamma[3].pos)


=============================================================================