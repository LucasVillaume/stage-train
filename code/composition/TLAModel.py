import copy

######## Deux fonctions pour convertir le "format" des events ########
def opDir(dir):
    return "R" if dir == "L" else "L"

def format_events(trains, events):
    tokens = [0]*9 #un token par canton
    numEv = [-1,-1,-1]
    wait_list = []
    train_list = [x for x in range(len(trains))]
    run_events = copy.deepcopy(events)
    run_program = [copy.deepcopy(x.prog) for x in trains]
    dict_events = {}
    precBlock = [-1,-1,-1] #dernier canton de chaque train

    while len(train_list) > 0:
        current = train_list.pop(0)
        flag = False

        if run_program[current] != [] and run_program[current][0][0] == "sync":
            run_program[current].pop(0)
        
        while len(run_events[current]) > 0 and not flag:
            event = run_events[current].pop(0)
            numEv[current] += 1

            if len(trains[current].prog) > 0:
                block = trains[current].troncons[numEv[current]]
                direction = run_program[current][0][1]
                c1 = str(block)+opDir(direction) #capteur du canton actuel
                c2 = str(precBlock[current])+direction #capteur du canton précédent
                precBlock[current] = block

                if numEv[current] == 0: #premier event
                    if len(event) > 0: 
                        dict_events[str(block)+direction] = [event]
                else:
                    if c1 not in dict_events:
                        dict_events[c1] = [event]
                    else:
                        dict_events[c1].append(event)

                    if c2 not in dict_events:
                        dict_events[c2] = [[]]
                    else:
                        dict_events[c2].append([])
                    #print(f"Add {c2} : []] / {c1} : [{event}]")

                    #Gère les programmes de train
                    run_program[current][0][2].pop(0)
                    if len(run_program[current][0][2]) == 0:
                        run_program[current].pop(0)
                    if run_program[current] != [] and run_program[current][0][0] == "sync":
                        run_program[current].pop(0)

            if len(event) > 0:
                for order in event:
                    if order[0] == "att":
                        jeton = int(order[1])
                        value = int(order[2])
                        if tokens[int(jeton)] == value: #attend pas
                            continue
                        else: # attend
                            wait_list.append((current, jeton, value)) #order[1] = jeton, order[2] = value
                            flag = True
                    elif order[0] == "incr":
                        tokens[int(order[1])] += 1
                        for w in range(len(wait_list)):
                            if wait_list[w][1] == int(order[1]) and wait_list[w][2] == tokens[int(order[1])]:
                                train_list.append(wait_list[w][0])
                                del wait_list[w]
                                break
                    else: #order[0] : auth ou turn
                        continue
    return dict_events


def progTraitement(prog):
    if len(prog) == 0:
        return "<<>>"

    progTmp = []

    for i in range(len(prog)):
        if prog[i][0] == "SU":
            if i-1 >= 0 and prog[i-1][0] == "sync":
                if i-2 >= 0:
                    if prog[i-2][1] != prog[i][1]: #direction différente
                        progTmp.append(('Start', prog[i][1]))
                else: #sync au début
                    progTmp.append(('Start', prog[i][1]))
            else: #début ou pas de sync avant
                progTmp.append(('Start', prog[i][1]))
            progTmp.append(('Until', prog[i][2])) #[int(x) for x in prog[i][2]]))
        else: # "sync"
            progTmp.append(prog[i])

    mprog = str(progTmp).replace("'", '"').replace("[", "<<").replace("]", ">>").replace("(", "<<").replace(")", ">>")
    return mprog

def eventTraitement(evs):
    events = copy.deepcopy(evs)
    for e in events:
        for i in range(len(e)):
            for j in range(len(e[i])):
                if e[i][j][0] == "turn":
                    tmp = list(e[i][j])
                    tmp[1] = int(tmp[1])-8 #pour numéroter à partir de 1 et non de 9
                    e[i][j] = tuple(tmp)
    return events





def trajet2model(trajet):
    model = "----------------------------- MODULE composition -----------------------------\n\n"+\
             "EXTENDS Integers, TLC, Sequences\n"+\
             "VARIABLE gamma, reg, sigma, feux, meta, rule\n\n"
    gamma = ""
    mtrains = ""
    tl = ""
    mevents = 'events == [x \in (1..8) \X {"L","R"} |-> << >>] '
    maxVal = 5
    buffer = []

    #trains et events et feux de circulation
    for i in range(len(trajet.trains)):
        gamma += "train"+str(i+1)
        gamma += ", " if i < len(trajet.trains) - 1 else ""
        mtrains += f"train{i+1} == [\n"+\
                 f"\tid |-> {i+1},\n"+\
                 f"\tpos |-> {trajet.trains[i].dep[0]},\n"+\
                 f"\tdir |-> \"*\",\n"+\
                 f"\tprog |-> {progTraitement(trajet.trains[i].prog)},\n"+\
                 f"\ttpos |-> {trajet.trains[i].dep[0]}\n]\n"


    formatEvent = format_events(trajet.trains, eventTraitement(trajet.events))
    
    for k,v in sorted(formatEvent.items()):
        pos = k[0]
        direction = k[1]
        if mevents == 'events == [x \in (1..8) \X {"L","R"} |-> << >>] ':
            mevents =  mevents[:10] + "[" + mevents[10:]
            mevents += f'EXCEPT ![{pos},"{direction}"] = {str(v).replace("[", "<<").replace("]", ">>").replace("(", "<<").replace(")", ">>").replace("'", '"')}'
        else:
            mevents += f'\t\t\t\t\t\t\t\t\t\t ![{pos},"{direction}"] = {str(v).replace("[", "<<").replace("]", ">>").replace("(", "<<").replace(")", ">>").replace("'", '"')}'
        mevents += ",\n" if k != sorted(formatEvent.keys())[-1] else "]\n" #todo: eviter de trier à chaque fois

    #events au démarrage
    for i in range(len(trajet.trains)):
        if trajet.trains[i].prog != [] and trajet.trains[i].prog[0][0] == "sync":
            buffer.append([trajet.trains[i].troncons[0], trajet.trains[i].prog[1][1]]) #sync toujours suivie par un start
    buffer = str(buffer).replace("'", '"').replace("[", "<<").replace("]", ">>")

    #First stop
    for i in range(len(trajet.trains)):
        stop = trajet.checkpoints[i][0]
        if stop != -1:
            if tl == "":
                tl += f'EXCEPT ![{stop},"L"] = "R",\n\t\t\t\t\t     ![{stop},"R"] = "R"'
            else:
                tl += f',\n\t\t\t\t\t     ![{stop},"L"] = "R",\n\t\t\t\t\t     ![{stop},"R"] = "R"'
    tl = f"[traffic_lights {tl}]" if tl != "" else "traffic_lights"


    #initialisation
    model += mtrains + "\n\n" + mevents
    model += f"token == [x \\in 1..8 |-> 0]\nwait == [x \\in (1..8) \\X (0..{maxVal}) |-> -1]\n"
    model += 'traffic_lights == [x \\in (1..8) \\X {"L","R"} |-> "V"]\n'
    model += f"histo == {str(trajet.histo).replace("'", '"').replace("[", "<<").replace("]", ">>")}\n"
    model += f"checkpoint == {str(trajet.checkpoints).replace("[", "<<").replace("]", ">>").replace("(", "<<").replace(")", ">>")}\n"

   
    #aiguillages
    switch = "switch == <<"
    cpt = 0
    for etat,_ in trajet.switch_init.values():
        switch += f'"{etat}"'
        switch += ", " if cpt < len(trajet.switch_init) - 1 else ""
        cpt += 1
    switch += ">>\n\n"
    model +=  switch


    #Init
    init = "Init ==\n" + \
            f"    /\\ gamma = <<{gamma}>>\n"+\
            f"    /\\ reg = [\n"+\
            "\t\tE |-> events,\n"+\
            "\t\tJ |-> token,\n"+\
            "\t\tW |-> {},\n"+\
            "\t\tH |-> histo,\n"+\
            "\t\tCP |-> checkpoint\n    \t]\n"+\
            f"    /\\ sigma = switch\n"+\
            f"    /\\ feux = {tl}\n"+\
            f"    /\\ meta = [\n" + \
            f"\t\tmsg   |-> << {buffer}, <<>> >>,\n" + \
            "\t\tgarde |-> [state |-> \"none\", requests |-> <<>>]\n    \t]\n" + \
            f"    /\\ rule = \"\"\n\n"

    property = "Liveness ==\n" + \
               f"    /\\ <>[] /\\ gamma[1].pos = {trajet.trains[0].arr[0]}\n" + \
                "            /\\ gamma[1].dir = \"*\"\n" + \
               f"    /\\ <>[] /\\ gamma[2].pos = {trajet.trains[1].arr[0]}\n" + \
                "            /\\ gamma[2].dir = \"*\"\n" + \
               f"    /\\ <>[] /\\ gamma[3].pos = {trajet.trains[2].arr[0]}\n" + \
                "            /\\ gamma[1].dir = \"*\"\n"

    property += "\nSafety ==\n" + \
                "    /\\ [] (gamma[1].pos /= gamma[2].pos /\\ gamma[1].pos /= gamma[3].pos /\\ gamma[2].pos /= gamma[3].pos)\n"

    model += init+property + "\n\n"


    return model+"============================================================================="

