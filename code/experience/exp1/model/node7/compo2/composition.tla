----------------------------- MODULE composition -----------------------------

EXTENDS Integers, TLC, Sequences
VARIABLE gamma, reg, sigma, feux, meta, rule

train1 == [
	id |-> 1,
	pos |-> 3,
	dir |-> "*",
	prog |-> <<<<"StartUntil", "R", <<4, 6, 7, 3, 4, 6>>>>>>
]
train2 == [
	id |-> 2,
	pos |-> 2,
	dir |-> "*",
	prog |-> <<>>
]
train3 == [
	id |-> 3,
	pos |-> 5,
	dir |-> "*",
	prog |-> <<>>
]


events == <<
    <<<<3, <<>>>>, <<4, <<>>>>, <<6, <<>>>>, <<7, <<<<"turn", 3, "d">>, <<"auth">>>>>>, <<3, <<<<"turn", 2, "d">>, <<"auth">>>>>>, <<4, <<<<"turn", 5, "v">>, <<"auth">>>>>>, <<6, <<>>>>>>,
    <<<<2, <<>>>>>>,
    <<<<5, <<>>>>>>
>>

token == [x \in 1..8 |-> 0]
wait == [x \in (1..8) \X (0..4) |-> -1]
traffic_lights == [x \in (1..8) \X {"L","R"} |-> "V"]
switch == <<"d", "d", "d", "v", "v">>

Init ==
    /\ gamma = <<train1, train2, train3>>
    /\ reg = [
		E |-> events,
		J |-> token,
		W |-> {}
    	]
    /\ sigma = switch
    /\ feux = [traffic_lights EXCEPT 
			![7,"L"] = "R",
			![7,"R"] = "R",
			![2,"L"] = "R",
			![2,"R"] = "R",
			![5,"L"] = "R",
			![5,"R"] = "R"]
    /\ meta = [
		msg   |-> << <<>>, <<>> >>,
		garde |-> [state |-> "none", requests |-> <<>>]
    	]
    /\ rule = ""

Liveness ==
    /\ <>[] /\ gamma[1].pos = 6
            /\ gamma[1].dir = "*"
    /\ <>[] /\ gamma[2].pos = 2
            /\ gamma[2].dir = "*"
    /\ <>[] /\ gamma[3].pos = 5
            /\ gamma[1].dir = "*"

Safety ==
    /\ [] (gamma[1].pos /= gamma[2].pos /\ gamma[1].pos /= gamma[3].pos /\ gamma[2].pos /= gamma[3].pos)


=============================================================================