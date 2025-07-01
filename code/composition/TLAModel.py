

def progTraitement(prog):
    if len(prog) == 0:
        return "<<>>"

    for i in range(len(prog[0][2])):
        tmp = list(prog[0])
        tmp[2][i] = int(tmp[2][i])
        prog[0] = tuple(tmp)

    mprog = str(prog).replace("'", '"').replace("[", "<<").replace("]", ">>").replace("(", "<<").replace(")", ">>")
    mprog = mprog.replace("SU", "StartUntil")
    return mprog

def eventTraitement(event, troncons):
    for i in range(len(event)):
        for j in range(len(event[i])):
            if event[i][j][0] == "turn":
                tmp = list(event[i][j])
                tmp[1] = int(tmp[1])-8 #pour numéroter à partir de 1 et non de 9
                event[i][j] = tuple(tmp)
        event[i] = [troncons[i], event[i]]
    return event

def trajet2model(trajet,troncons):
    model = "----------------------------- MODULE composition -----------------------------\n\n"+\
             "EXTENDS Integers, TLC, Sequences\n"+\
             "VARIABLE gamma, reg, sigma, feux, meta, rule\n\n"
    gamma = ""
    mtrains = ""
    tl = ""
    mevents = "events == <<\n"
    maxVal = 4

    #trains et events et feux de circulation
    for i in range(len(trajet.trains)):
        gamma += "train"+str(i+1)
        gamma += ", " if i < len(trajet.trains) - 1 else ""
        mtrains += f"train{i+1} == [\n"+\
                 f"\tid |-> {i+1},\n"+\
                 f"\tpos |-> {trajet.trains[i].dep[0]},\n"+\
                 f"\tdir |-> \"*\",\n"+\
                 f"\tprog |-> {progTraitement(trajet.trains[i].prog)}\n]\n"
        
        mevents += f"    {eventTraitement(trajet.events[i], troncons[i])}"
        mevents += ",\n" if i < len(trajet.trains) - 1 else "\n"

        stop = [x[1] for x in trajet.wait_list if x[0] == trajet.trains[i].id][0]
        tl += f'\t\t\t![{stop},"L"] = "R",\n\t\t\t![{stop},"R"] = "R"'
        tl += f",\n" if i < len(trajet.trains) - 1 else "" 
    
    mevents += ">>\n\n"
    mevents = mevents.replace("[", "<<").replace("]", ">>").replace("(", "<<").replace(")", ">>").replace("'", '"')

    #initialisation
    model += mtrains + "\n\n" + mevents
    model += f"token == [x \\in 1..8 |-> 0]\nwait == [x \\in (1..8) \\X (0..{maxVal}) |-> -1]\n"
    model += 'traffic_lights == [x \\in (1..8) \\X {"L","R"} |-> "V"]'

    
    #aiguillages
    switch = "\nswitch == <<"
    cpt = 0
    for etat,_ in trajet.switch_init.values():
        switch += f'"{etat}"'
        switch += ", " if cpt < len(trajet.switch_init) - 1 else "" 
        cpt += 1
    switch += ">>\n\n"
    model +=  switch

    wait = "{"
    for w in trajet.wait_list:
        wait += f"<<{w[0]+1},{int(w[1])},{int(w[2])},{w[3]}>>"
        wait += ", " if w != trajet.wait_list[-1] else ""
    wait += "}"

    #Init
    init = "Init ==\n" + \
            f"    /\\ gamma = <<{gamma}>>\n"+\
            f"    /\\ reg = [\n"+\
            "\t\tE |-> events,\n"+\
            "\t\tJ |-> token,\n"+\
            f"\t\tW |-> {wait}\n    \t]\n"+\
            f"    /\\ sigma = switch\n"+\
            f"    /\\ feux = [traffic_lights EXCEPT \n{tl}]\n"+\
            f"    /\\ meta = [\n" + \
            "\t\tmsg   |-> << <<>>, <<>> >>,\n" + \
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

