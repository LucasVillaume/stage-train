import copy

"""
Prototype largement améliorable
Todo : refaire proprement certaines parties
"""




def check_properties(first, second):
    """
    first : ([train1, train2, ..., trainN], [aig_init, aig_final])
    """
    for i in range(2):
        for j in range(len(first[i])):
            if first[i][j][1] != second[i][j][0]: # x[i][j][0] = pos/dir init  | x[i][j][1] = pos/dir final 
                error = "directions ou positions différentes" if i == 0 else "aiguillages différents"
                print(f"Erreur : {error}")
                return False
    return True


def merge_program(first, second):
    """
    fusionne un à un les programmes des trains
    first : [train1, train2, ..., trainN]
    """
    for i in range(len(first)):
        first[i] += second[i]
        ordre_train = copy.deepcopy(first[i])
        for o in range(len(first[i])-1):
            _, direction, _ = first[i][o]
            _, direction2, _ = first[i][o+1]
            if direction == direction2:
                ordre_train.remove(first[i][o])
        first[i] = ordre_train
    return first


def update_tokens(first, second, nbTokens):
    """
    first : [events_t1, events_t2, ..., events_tN]
    """
    

    token = [0]*nbTokens
    for events in first:
        for event in events:
            for order in event:
                if len(order) > 0 and order[0] == "incr":
                    token[order[1]] += 1
    for train in range(len(second)):
        for events in range(len(second[train])):
            for o in range(len(second[train][events])):
                order = second[train][events][o]
                if len(order) > 0 and order[0] == "att":
                    order = list(order) #aberration 
                    order[2] += token[order[1]]
                    second[train][events][o] = tuple(order) #aberration 

    return second


def merge_events(first, second):
    """
    first : [events_t1, events_t2, ..., events_tN]
    """
    for t in range(len(first)):
        first[t][-1] += second[t][0]
        second[t].pop(0)
        first[t] += second[t]
    return first


def composition(first, sec, nbTokens=4):
    """
    first : (trains, events, aiguillages)
    """
    
    f_check = [first["gamma"],first["switch"]]
    s_check = [sec["gamma"],sec["switch"]]

    #vérification des propriétés
    if check_properties(f_check, s_check) != True:
        return False
    
    fm = [x[2] for x in first["gamma"]]
    sm = [x[2] for x in sec["gamma"]]

    #fusion des programmes
    new_prog = merge_program(fm, sm)

    #remplace les programmes initiaux par les nouveaux
    for t in range(len(new_prog)):
        first["gamma"][t] = list(first["gamma"][t]) #aberration
        first["gamma"][t][2] = new_prog[t]
        first["gamma"][t] = tuple(first["gamma"][t]) #aberration
   
    #mise à jour des tokens
    update_tokens(first["events"], sec["events"], nbTokens)

    #fusion des events
    merge_events(first["events"], sec["events"])

    return first




if __name__ == "__main__":
    train1_1 = ("4*","8*",[("SU","L",8)]) #(pos, dir, target, Tdir, P)
    train2_1 = ("5*","3*",[("SU","R",3)]) #(pos, dir, target, Tdir, P)
    switch1_init = ["d","d","v","d","d"]
    switch1_final = ["d","d","d","d","d"]
    event_t1_1 = [[],[],[("turn",3,"d"),("incr",3)]]
    event_t2_1 = [[],[("att",3,1)],[]]

    first = {
        "gamma" : [train1_1, train2_1],
        "switch" : [switch1_init, switch1_final],
        "events" : [event_t1_1, event_t2_1]
    }


    train1_2 = ("8*","7*",[("SU","R",3),("SU","L",7)]) #(pos, dir, target, Tdir, P)
    train2_2 = ("3*","3*",[("SU","R",4),("SU","L",3)]) #(pos, dir, target, Tdir, P)
    switch2_init = ["d","d","d","d","d"]
    switch2_final = ["d","d","d","d","d"]
    event_t1_2 = [[("att",3,1)],[("turn",3,"d"),("auth","")],[("incr",3)]]
    event_t2_2 = [[],[("turn",3,"v"),("incr",3),("att",3,2)],[]]

    second = {
        "gamma" : [train1_2, train2_2],
        "switch" : [switch2_init, switch2_final],
        "events" : [event_t1_2, event_t2_2]
    }


    res = composition(first, second)
    for k,v in res.items():
        print(f"{k} :")
        if k == "gamma" or k == "events":
            for sub in v:
                print(f"\t{sub}")

