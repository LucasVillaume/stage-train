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
	pos |-> 5,
	dir |-> "*",
	prog |-> <<>>
]
train3 == [
	id |-> 3,
	pos |-> 4,
	dir |-> "*",
	prog |-> <<<<"StartUntil", "L", <<3, 7, 6>>>>>>
]


events == <<
    <<<<8, <<>>>>, <<3, <<>>>>, <<2, <<<<"turn", 2, "d">>, <<"incr", 3>>>>>>>>,
    <<<<5, <<>>>>>>,
    <<<<4, <<<<"att", 3, 1>>>>>>, <<3, <<<<"turn", 3, "d">>, <<"auth">>>>>>, <<7, <<<<"turn", 4, "v">>, <<"auth">>>>>>, <<6, <<>>>>>>
>>

token == [x \in 1..8 |-> 0]
wait == [x \in (1..8) \X (0..4) |-> -1]
traffic_lights == [x \in (1..8) \X {"L","R"} |-> "V"]
switch == <<"v", "v", "v", "d", "d">>

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
			![5,"L"] = "R",
			![5,"R"] = "R",
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
    /\ <>[] /\ gamma[2].pos = 5
            /\ gamma[2].dir = "*"
    /\ <>[] /\ gamma[3].pos = 6
            /\ gamma[1].dir = "*"

Safety ==
    /\ [] (gamma[1].pos /= gamma[2].pos /\ gamma[1].pos /= gamma[3].pos /\ gamma[2].pos /= gamma[3].pos)


=============================================================================