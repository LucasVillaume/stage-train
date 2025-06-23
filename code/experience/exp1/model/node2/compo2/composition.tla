----------------------------- MODULE composition -----------------------------

EXTENDS Integers, TLC, Sequences
VARIABLE gamma, reg, sigma, feux, meta, rule

train1 == [
	id |-> 1,
	pos |-> 6,
	dir |-> "*",
	prog |-> <<<<"StartUntil", "R", <<7, 3, 1>>>>>>
]
train2 == [
	id |-> 2,
	pos |-> 4,
	dir |-> "*",
	prog |-> <<>>
]
train3 == [
	id |-> 3,
	pos |-> 5,
	dir |-> "*",
	prog |-> <<<<"StartUntil", "R", <<7, 3, 2>>>>>>
]


events == <<
    <<<<6, <<<<"att", 7, 1>>>>>>, <<7, <<<<"att", 3, 1>>>>>>, <<3, <<<<"turn", 1, "d">>, <<"auth">>>>>>, <<1, <<>>>>>>,
    <<<<4, <<>>>>>>,
    <<<<5, <<>>>>, <<7, <<>>>>, <<3, <<<<"turn", 4, "v">>, <<"incr", 7>>>>>>, <<2, <<<<"incr", 3>>>>>>>>
>>

token == [x \in 1..8 |-> 0]
wait == [x \in (1..8) \X (0..4) |-> -1]
traffic_lights == [x \in (1..8) \X {"L","R"} |-> "V"]
switch == <<"v", "v", "d", "d", "d">>

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
			![4,"L"] = "R",
			![4,"R"] = "R",
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