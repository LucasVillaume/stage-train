----------------------------- MODULE composition -----------------------------

EXTENDS Integers, TLC, Sequences
VARIABLE gamma, reg, sigma, feux, meta, rule

train1 == [
	id |-> 1,
	pos |-> 2,
	dir |-> "*",
	prog |-> <<<<"StartUntil", "L", <<3, 7, 6>>>>>>
]
train2 == [
	id |-> 2,
	pos |-> 5,
	dir |-> "*",
	prog |-> <<<<"StartUntil", "R", <<7, 3, 1>>>>>>
]
train3 == [
	id |-> 3,
	pos |-> 6,
	dir |-> "*",
	prog |-> <<<<"StartUntil", "L", <<4>>>>>>
]


events == <<
    <<<<2, <<<<"att", 3, 1>>>>>>, <<3, <<>>>>, <<7, <<<<"att", 6, 1>>>>>>, <<6, <<>>>>>>,
    <<<<5, <<>>>>, <<7, <<<<"turn", 4, "v">>>>>>, <<3, <<>>>>, <<1, <<<<"turn", 1, "v">>, <<"turn", 2, "v">>, <<"incr", 3>>>>>>>>,
    <<<<6, <<>>>>, <<4, <<<<"incr", 6>>>>>>>>
>>

token == [x \in 1..8 |-> 0]
wait == [x \in (1..8) \X (0..4) |-> -1]
traffic_lights == [x \in (1..8) \X {"L","R"} |-> "V"]
switch == <<"d", "v", "d", "d", "v">>

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
    /\ <>[] /\ gamma[1].pos = 6
            /\ gamma[1].dir = "*"
    /\ <>[] /\ gamma[2].pos = 1
            /\ gamma[2].dir = "*"
    /\ <>[] /\ gamma[3].pos = 4
            /\ gamma[1].dir = "*"

Safety ==
    /\ [] (gamma[1].pos /= gamma[2].pos /\ gamma[1].pos /= gamma[3].pos /\ gamma[2].pos /= gamma[3].pos)


=============================================================================