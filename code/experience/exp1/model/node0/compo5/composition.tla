----------------------------- MODULE composition -----------------------------

EXTENDS Integers, TLC, Sequences
VARIABLE gamma, reg, sigma, feux, meta, rule

train1 == [
	id |-> 1,
	pos |-> 8,
	dir |-> "*",
	prog |-> <<<<"StartUntil", "R", <<3, 4, 6, 7, 3, 1>>>>>>
]
train2 == [
	id |-> 2,
	pos |-> 5,
	dir |-> "*",
	prog |-> <<<<"StartUntil", "L", <<4>>>>>>
]
train3 == [
	id |-> 3,
	pos |-> 2,
	dir |-> "*",
	prog |-> <<>>
]


events == <<
    <<<<8, <<>>>>, <<3, <<>>>>, <<4, <<>>>>, <<6, <<<<"turn", 5, "d">>, <<"incr", 4>>>>>>, <<7, <<<<"turn", 3, "d">>, <<"auth">>>>>>, <<3, <<<<"turn", 2, "v">>, <<"turn", 1, "d">>, <<"auth">>>>>>, <<1, <<>>>>>>,
    <<<<5, <<<<"att", 4, 1>>>>>>, <<4, <<>>>>>>,
    <<<<2, <<>>>>>>
>>

token == [x \in 1..8 |-> 0]
wait == [x \in (1..8) \X (0..4) |-> -1]
traffic_lights == [x \in (1..8) \X {"L","R"} |-> "V"]
switch == <<"d", "d", "v", "v", "v">>

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
			![5,"L"] = "R",
			![5,"R"] = "R",
			![2,"L"] = "R",
			![2,"R"] = "R"]
    /\ meta = [
		msg   |-> << <<>>, <<>> >>,
		garde |-> [state |-> "none", requests |-> <<>>]
    	]
    /\ rule = ""

Liveness ==
    /\ <>[] /\ gamma[1].pos = 1
            /\ gamma[1].dir = "*"
    /\ <>[] /\ gamma[2].pos = 4
            /\ gamma[2].dir = "*"
    /\ <>[] /\ gamma[3].pos = 2
            /\ gamma[1].dir = "*"

Safety ==
    /\ [] (gamma[1].pos /= gamma[2].pos /\ gamma[1].pos /= gamma[3].pos /\ gamma[2].pos /= gamma[3].pos)


=============================================================================