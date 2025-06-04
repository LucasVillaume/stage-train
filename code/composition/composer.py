import json
import re
import copy
from TLAModel import trajet2model


maquette = {
    '1L' : {3: "9d10v"},

    '2L' : {3: "9v10v"},

    '3L' : {7: "11d", 8: "11v"},
    '3R' : {4: "10d", 1: "9d10v", 2: "9v10v"},

    '4L' : {3:  "10d"},
    '4R' : {5: "13d", 6: "13v"},

    '5L' : {4: "13d"},
    '5R' : {7: "12d"},

    '6L' : {4: "13v"},
    '6R' : {7: "12v"},

    '7L' : {5: "12d", 6: "12v"},
    '7R' : {3: "11d"},

    '8R' : {3: "11v"}
}



class Train:
    def __init__(self, id, depart, arrivee, nb_trains):
        self.id = id
        self.dep = depart
        self.arr = arrivee
        self.prog = []
        self.last_crit = [0]*nb_trains #position du dernier critique
        self.offset_crit = [0]*nb_trains
        self.troncons = []

    def __str__(self):
        return f"T{self.id} {self.dep} -> {self.arr} : P{self.prog} / T{self.troncons} / C{self.last_crit}"
    
class Trajet:
    def __init__(self, trains, events):
        self.trains = trains
        self.events = events
        # "numAiguillage" : ("état", "free") / free à False si l'aiguillage doit être ainsi dans l'état initial
        self.switch_init = {"9": ("d",True), "10": ("d",True), "11": ("d",True), "12": ("d",True), "13": ("d",True)}
        self.histo_switch = {"9": [], "10": [], "11": [], "12": [], "13": []} #pour l'historique des aiguillages
        self.tokens = [0]*9 #un token par canton
        self.first_stop = self.firstStop()

    def firstStop(self):
        first_stop = [-1]*len(self.trains)
        for i in range(len(self.trains)):
            first_stop[i] = self.trains[i].troncons[-1]
        return first_stop

    def __str__(self):
        string = ""
        for i in range(len(self.trains)):
            string += f"{str(self.trains[i])}\n"
            string += f"  Events : {self.events[i]}\n"
            string += f"  Tokens : {self.tokens}\n"
            string += f"  First stop : {self.first_stop[i]}\n"
        return string



def parseTrain(depart, arrivee, nb_trains):
    trains = []
    for i in range(nb_trains):
        pos_d= re.findall(r'\d+', depart)[i]
        dir_d = re.findall(r'[RL*]', depart)[i]

        pos_e = re.findall(r'\d+', arrivee)[i]
        dir_e = re.findall(r'[RL*]', arrivee)[i]
        trains.append(Train(i,(pos_d, dir_d), (pos_e, dir_e), nb_trains))
    return trains



def getTroncons(train, events, circuit):
    switch = {"9": "d", "10": "d", "11": "d", "12": "d", "13": "d"}
    pos, dirT = train.dep
    troncons = [int(pos)]

    for i in range(len(events)-1):
        for order in events[i]:
            if order[0] == "turn":
                switch[order[1]] = order[2]

        #prochaine position possible
        if str(pos)+dirT in circuit:
            next_pos = circuit[str(pos)+dirT]
            #peu élégant, transforme le dict en str
            str_s = "".join([k+v for k, v in switch.items()])
            for neigh, aig in next_pos.items(): 
                if aig in str_s:
                    troncons.append(neigh)
                    pos = neigh
                    break
    train.troncons = troncons



def createProgram(start, end, paths, nb_trains=3):
    trains = parseTrain(start, end, nb_trains)
    events = [[[]], [[]], [[]]]

    #construit les events
    for tr in range(nb_trains):
        path = paths[tr]
        if path != "":
            steps = path.split("/")
            for s in range(len(steps)):
                if int(steps[s][:-1]) > 8:
                    numEv = len(events[tr])-1
                    events[tr][numEv].append(("turn",steps[s][:-1],steps[s][-1]))
                    events[tr].append([]) 
                    if s+1 < len(steps): #TODO Super sale donc voir pour arranger
                        if (int(steps[s][:-1]) in [9,10] and int(steps[s+1][:-1]) in [9,10]):
                            events[tr].pop() #supprime le dernier event
    #assigne les troncons
    for i in range(len(trains)):
        getTroncons(trains[i], events[i], maquette)
    
    #construit le programme des trains
    for i in range(nb_trains):
        if trains[i].arr[1] != "*":
            trains[i].prog.append(("SU",trains[i].arr[1],trains[i].troncons[1:]))

    #construit l'historique des aiguillages pour le sillon
    histo_switch = {"9": [], "10": [], "11": [], "12": [], "13": []}
    for t in range(len(events)):
        for e in range(len(events[t])):
            for order in events[t][e]:
                if order[0] == "turn":
                    histo_switch[order[1]].append((t, e))

    sillon = Trajet(trains, events)
    sillon.histo_switch = histo_switch
    return sillon


def merge_historique(o1, o2):
    for k,v in o2.histo_switch.items():
        for train, event in v:
            o1.histo_switch[k].append((train, event + len(o1.events[train])-1))


def reduc_turns(t1,t2):
    for e2 in range(len(t2)):
        event2 = t2[e2]
        for o2 in range(len(t2[e2])):
            found = False
            for e1 in range(len(t1)-1,-1,-1):
                event1 = t1[e1]
                for o1 in range(len(t1[e1])):
                    if event2[o2][0] == "turn" and event1[o1][0] == "turn" and event2[o2][1] == event1[o1][1]:
                        found = True
                        if event2[o2][2] == event1[o1][2]:  # même état
                            del event2[o2]
                        break
                if found:
                    break
            if found:
                break



def clean_turns(o1):
    for t in range(len(o1.events)):
        cpy_eventsT = copy.deepcopy(o1.events[t])
        for e in range(len(o1.events[t])):
            if len(o1.events[t][e]) > 0:
                for i in range(len(o1.events[t][e])):
                    ordre = o1.events[t][e][i]
                    if ordre[0] == "turn":
                        if o1.switch_init[ordre[1]][1]: # aiguillage pas encore assigné
                            o1.switch_init[ordre[1]] = (ordre[2], False)
                            cpy_eventsT[e].remove(ordre)
        o1.events[t] = cpy_eventsT


def findCritical(t1, t2, o1):
    crit = []

    for i in range(len(t2.troncons)):
        endT1 = t1.last_crit[t2.id]
        for j in range(len(t1.troncons)-1, endT1-1, -1):
            if t2.troncons[i] == t1.troncons[j]:
                t2.offset_crit[t1.id] = len(o1.trains[t2.id].troncons) - 1
                crit.append(t2.troncons[i])
                t1.last_crit[t2.id] = j
                t2.last_crit[t1.id] = i
                break
    return crit


def handleCritical(t1, t2, crit, o2, o1):
    index_cI = 0
    index_cA = 0
    #cherche la sortie du canton critique dans o1
    for i in range(len(t1.troncons)-1, -1, -1):
        if t1.troncons[i] == crit:
            index_cI = i+1
            break

    #cherche l'entrée du canton critique dans o2
    for i in range(len(t2.troncons)-1):
        if t2.troncons[i+1] == crit: #+1 car on veut l'entrée du canton
            index_cA = i
            break

    cpy_eventsT = copy.deepcopy(o2.events[t2.id][index_cA])
    offset = 0
    for o in range(len(o2.events[t2.id][index_cA])):
        order = o2.events[t2.id][index_cA][o]
        if order[0] == "turn":
            index = o1.histo_switch[order[1]].index((t2.id, index_cA+len(o1.events[t2.id])-1))
            if index > 0:
                train, event = o1.histo_switch[order[1]][index-1] # prend le précédent
                if train != t1.id: #Pas vraiment utile, petit optimisation pour éviter des "auth" inutiles
                    o1.events[train][event+1].append(order)
                else:
                    o1.events[t1.id][index_cI].append(order)
            else:
                o1.events[t1.id][index_cI].append(order)
            del cpy_eventsT[o-offset]
            offset += 1
    o2.events[t2.id][index_cA] = cpy_eventsT

    o1.events[t1.id][index_cI].append(("incr", crit))
    o2.tokens[int(crit)] += 1
    o2.events[t2.id][index_cA].append(("att", crit, o2.tokens[int(crit)]))



def preparation(o1, o2):
    merge_historique(o1, o2)
    #traitez les aiguillage "critiques"
    for i in range(len(o1.trains)):
        for j in range(len(o2.trains)):
            if i != j: #pas clair ça, certainement à suprimer
                reduc_turns(o1.events[i], o2.events[j])
    clean_turns(o1)

    #traitez les ressources critiques
    for i in range(len(o1.trains)):
        for j in range(len(o2.trains)):
            if i != j:
                crit = findCritical(o1.trains[i], o2.trains[j], o1)
                if len(crit) > 0:
                    for canton_crit in crit:
                        handleCritical(o1.trains[i], o2.trains[j], canton_crit, o2, o1)

    #mise à jour des tokens pour att
    for i in range(len(o2.trains)):
        for j in range(len(o2.events[i])):
            for k in range(len(o2.events[i][j])):
                if o2.events[i][j][k][0] == "att":
                    jeton = o2.events[i][j][k][1]
                    value = o2.events[i][j][k][2]
                    o2.events[i][j][k] = ("att", jeton, value+o1.tokens[int(jeton)])            



def assemblage(o1, o2):
    trains = []
    events = []
    for i in range(len(o1.trains)):
        trains.append(Train(i, o1.trains[i].dep, o2.trains[i].arr, len(o1.trains)))
        #assemble programme de train
        trains[i].prog = o1.trains[i].prog + o2.trains[i].prog
        trains[i].troncons = o1.trains[i].troncons + o2.trains[i].troncons[1:]
        t1_lc = o1.trains[i].last_crit
        t2_lc = [x+y for x, y in zip(o2.trains[i].last_crit, o2.trains[i].offset_crit)]
        trains[i].last_crit = t2_lc if t2_lc > t1_lc else t1_lc # TODO: voir ça

        #assemble events
        events.append(o1.events[i])
        events[i][-1] += o2.events[i][0]
        events[i] += o2.events[i][1:]

    o3 = Trajet(trains, events)
    o3.switch_init = o1.switch_init
    o3.histo_switch = o1.histo_switch

    #assemble les tokens
    for i in range(len(o1.tokens)):
        o3.tokens[i] = o1.tokens[i] + o2.tokens[i]
    return o3


def findFirstStop(o1):
    for t in range(len(o1.trains)):
        found = False
        for e in range(len(o1.events[t])):
            for order in o1.events[t][e]:
                if order[0] == "att" or order[0] == "auth":
                    o1.first_stop[t] = o1.trains[t].troncons[e]
                    found = True
                    break
            if found:
                break
        

def addAuth(o1):
    for t in range(len(o1.trains)):
        for e in range(len(o1.events[t])):
            if len(o1.events[t][e]) > 0:
                only_turn = True
                for o in range(len(o1.events[t][e])):
                    if o1.events[t][e][o][0] != "turn":
                        only_turn = False
                        break
                    if only_turn and o == len(o1.events[t][e])-1:
                        o1.events[t][e].append(["auth"])



def nettoyage(o1):
    for i in range(len(o1.trains)):
        #programme de trains
        prog_tmp = copy.deepcopy(o1.trains[i].prog)
        offset = 0
        for j in range(len(o1.trains[i].prog)-1):
            if o1.trains[i].prog[j][1] == o1.trains[i].prog[j+1][1]: #même direction
                tmp = list(o1.trains[i].prog[j+1]) # bricolage temporaire
                tmp[2] = o1.trains[i].prog[j][2] + o1.trains[i].prog[j+1][2]
                prog_tmp[j+1-offset] = tuple(tmp)
                prog_tmp.remove(o1.trains[i].prog[j])
                offset += 1
        o1.trains[i].prog = prog_tmp

    addAuth(o1)
    findFirstStop(o1)
                        
def compose(o1, o2):
    """
    Compose les deux trajets o1 et o2 en un seul trajet.
    """
    # Préparation des trajets
    preparation(o1, o2)

    # Assemblage des trajets
    o3 = assemblage(o1, o2)

    # Nettoyage du trajet assemblé
    nettoyage(o3)

    return o3



if __name__ == "__main__":

    etats = dict()
    with open("etat_elem.json", "r") as file:
        etats = json.load(file)

    """s4_1 = etats["N4L5R2* -> N8L7R2*"].split("__")
    o1 = createProgram("N4L5R2*", "N8L7R2*",s4_1) 
    s4_2 = etats["N8L7R2* -> N8*4R2*"].split("__")
    o2 = createProgram("N8L7R2*", "N8*4R2*",s4_2)
    print(f"o1\n{o1}")
    print(f"o1 histo_switch : {o1.histo_switch}")
    print(f"o2\n{o2}")
    print(f"o2 histo_switch : {o2.histo_switch}")
    preparation(o1, o2)
    o3 = assemblage(o1, o2)
    nettoyage(o3)
    print(f"o3\n{o3}")
    print(f"o3 switch_init : {o3.switch_init}")
    print(f"o3 switch historique : {o3.histo_switch}")


    s5 = etats["N8*4R2* -> N8R4*2*"].split("__")
    o4 = createProgram("N8*4R2*", "N8R4*2*", s5)
    print(f"o4\n{o4}")
    o5 = compose(o3, o4)
    print(f"o5\n{o5}")
    print(f"o5 switch historique : {o5.histo_switch}")


    s6 = etats["N8R4*2* -> N3R4*2*"].split("__")
    o6 = createProgram("N8R4*2*", "N3R4*2*", s6)
    print(f"o6\n{o6}")
    o7 = compose(o5, o6)
    print(f"o7\n{o7}")
    print(f"o7 switch historique : {o7.histo_switch}") """

    """ s1 = etats["N2L7L6L -> N3L5L4L"].split("__")
    o1 = createProgram("N2L7L6L", "N3L5L4L", s1)
    s2 = etats["N3L5L4L -> N6L5*4*"].split("__")
    o2 = createProgram("N3L5L4L", "N6L5*4*", s2)
    print(f"o1\n{o1}")
    print(f"o2\n{o2}")
    o3 = compose(o1, o2)
    print(f"o3\n{o3}")
    print(f"o3 switch_init : {o3.switch_init}") """

    s1 = etats["N8*7R6* -> N8*5R6L"].split("__")
    o1 = createProgram("N8*7R6*", "N8*5R6L", s1)
    s2 = etats["N8*5R6L -> N8*2R4L"].split("__")
    o2 = createProgram("N8*5R6L", "N8*2R4L", s2)
    print(f"o1\n{o1}")
    print(f"o2\n{o2}")
    o3 = compose(o1, o2)
    print(f"o3\n{o3}")
    print(f"o3 switch_init : {o3.switch_init}")

