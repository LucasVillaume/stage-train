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
        self.troncons = []

    def __str__(self):
        return f"T{self.id} {self.dep} -> {self.arr} : P{self.prog} / T{self.troncons} / C{self.last_crit}"
    
class Trajet:
    def __init__(self, trains, events):
        self.trains = trains
        self.events = events
        # "numAiguillage" : ("état", "free") / free à False si l'aiguillage doit être ainsi dans l'état initial
        self.switch_init = {"9": ("d",True), "10": ("d",True), "11": ("d",True), "12": ("d",True), "13": ("d",True)}
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
            
    return Trajet(trains, events)



def findCritical(t1, t2):
    crit = [("",float('-inf'))]
    beginT1 = t1.last_crit[t2.id]
    beginT2 = t2.last_crit[t1.id]
    for i in range(beginT1,len(t1.troncons)):
        for j in range(beginT2,len(t2.troncons)):
            if t1.troncons[i] == t2.troncons[j]:
                if i-j > crit[0][1]:
                    crit = [(t1.troncons[i], i-j)]
                    t1.last_crit[t2.id] = i
                    t2.last_crit[t1.id] = j
                elif i-j == crit[0][1]:
                    crit.append((t1.troncons[i], i-j))
    return crit #renvoyer une liste des crit (si certains on le meme "score")



def handleCritical(t1, t2, crit, o2, o1):
    index_c = 0
    for i in range(len(t1.troncons)-1, -1, -1):
        if t1.troncons[i] == crit:
            index_c = i+1
            break
    for o in range(len(o2.events[t2.id][0])):
        order = o2.events[t2.id][0][o]
        if order[0] == "turn":
            o1.events[t1.id][index_c].append(order)
            del o2.events[t2.id][0][o]

    o1.events[t1.id][index_c].append(("incr", crit))
    o2.tokens[int(crit)] += 1
    o2.events[t2.id][0].append(("att", crit, o2.tokens[int(crit)]))



def preparation(o1, o2):
    #traitez les ressources critiques
    for i in range(len(o1.trains)):
        for j in range(len(o2.trains)):
            if i != j:
                crit = findCritical(o1.trains[i], o2.trains[j])
                if crit[0][0] != "":
                    for canton_crit in crit:
                        handleCritical(o1.trains[i], o2.trains[j], canton_crit[0], o2, o1)
    
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
        t2_lc = o2.trains[i].last_crit
        trains[i].last_crit = t2_lc if t2_lc > t1_lc else t1_lc    

        #assemble events
        events.append(o1.events[i])
        events[i][-1] += o2.events[i][0]
        events[i] += o2.events[i][1:]

    o3 = Trajet(trains, events)
    o3.switch_init = o1.switch_init

    #assemble les tokens
    for i in range(len(o1.tokens)):
        o3.tokens[i] = o1.tokens[i] + o2.tokens[i]
    return o3


def findFirstStop(o1):
    for t in range(len(o1.trains)):
        for e in range(len(o1.events[t])):
            for order in o1.events[t][e]:
                if order[0] == "att" or order[0] == "stop":
                    o1.first_stop[t] = o1.trains[t].troncons[e]
                    break
            """ if o1.first_stop[t] == -1:  # Si pas de stop trouvé, on prend le dernier tronçon
                o1.first_stop[t] = o1.trains[t].troncons[-1] """

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

        #events
        events_tmp = copy.deepcopy(o1.events[i])
        #events[i] : events de train i / events[i][j] : jème event / #events[i][j][k] : kème ordre
        for j in range(len(o1.events[i])):
            for k in range(len(o1.events[i][j])):
                if o1.events[i][j][k][0] == "turn":
                    aig = o1.events[i][j][k][1]
                    state = o1.events[i][j][k][2]
                    if o1.switch_init[aig][1]: #si l'aiguillage est libre
                        o1.switch_init[aig] = (state, False) #on le bloque
                        events_tmp[j].remove(o1.events[i][j][k])
        o1.events[i] = events_tmp
    findFirstStop(o1)
    addAuth(o1)
                        
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

    """ s4_1 = etats["N4L5R2* -> N8L7R2*"].split("__")
    o1 = createProgram("N4L5R2*", "N8L7R2*",s4_1) 
    s4_2 = etats["N8L7R2* -> N8*4R2*"].split("__")
    o2 = createProgram("N8L7R2*", "N8*4R2*",s4_2)
    print(f"o1\n{o1}")
    print(f"o2\n{o2}")
    preparation(o1, o2)
    o3 = assemblage(o1, o2)
    nettoyage(o3)
    print(f"o3\n{o3}")
    print(f"o3 switch_init : {o3.switch_init}") """

    s4_1 = etats["N8R5*7L -> N2R5*4L"].split("__")
    o1 = createProgram("N8R5*7L", "N2R5*4L", s4_1)
    print(f"o1\n{o1}")
    from TLAModel import trajet2model
    model = trajet2model(o1)
    print(model)

