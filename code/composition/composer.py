import json
import re
import copy
from TLAModel import trajet2model
import pickle


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
"""


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

        for j in range(len(trains[i].last_crit)):
            trains[i].last_crit[j] = t2_lc[j] if t2_lc[j] > t1_lc[j] else t1_lc[j]
        #trains[i].last_crit = t2_lc if t2_lc > t1_lc else t1_lc

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
                for o in range(len(o1.events[t][e])):
                    if o1.events[t][e][o][0] == "turn" and (t,e) in o1.histo_switch[o1.events[t][e][o][1]]:
                        o1.events[t][e].append(["auth"])
                        break



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
    
    #Compose les deux trajets o1 et o2 en un seul trajet.

    # Préparation des trajets
    preparation(o1, o2)

    # Assemblage des trajets
    o3 = assemblage(o1, o2)

    # Nettoyage du trajet assemblé
    nettoyage(o3)

    return o3"""





class Train:
    def __init__(self, id, depart, arrivee, nb_trains):
        self.id = id
        self.dep = depart
        self.arr = arrivee
        self.prog = []
        self.last_crit = [0]*nb_trains #position du dernier critique
        self.troncons = []

    def __str__(self):
        return f"T{self.id} {self.dep} -> {self.arr} : P{self.prog}"
    
class Trajet:
    def __init__(self, trains, events):
        self.trains = trains
        self.events = events
        # "numAiguillage" : ("état", "free") / free à False si l'aiguillage doit être ainsi dans l'état initial
        self.switch_init = {"9": ("d",True), "10": ("d",True), "11": ("d",True), "12": ("d",True), "13": ("d",True)}
        self.histo_switch = {"9": [], "10": [], "11": [], "12": [], "13": []} #pour l'historique des aiguillages
        self.wait_list = [] # liste d'attente pour les trains
        self.posInitial = ""
        self.posFinal = ""
        #self.tokens = [0]*9 #un token par canton
        #self.first_stop = [] #(id,pos)

    """ def firstStop(self):
        first_stop = [-1]*len(self.trains)
        for i in range(len(self.trains)):
            first_stop[i] = self.trains[i].troncons[-1]
        return first_stop """

    def __str__(self):
        string = ""
        for i in range(len(self.trains)):
            string += f"{str(self.trains[i])}\n"
            string += f"  Events : {self.events[i]}\n"
        string += f"Histo switch : {self.histo_switch}\nWaiting list : {self.wait_list}\nposInitial : {self.posInitial} | posFinal : {self.posFinal}\n"
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

    for i in range(len(trains)):
        getTroncons(trains[i], events[i], maquette) 
       
    #construit le programme des trains
    for i in range(nb_trains):
        if trains[i].arr[1] != "*":
            trains[i].prog.append(("SU",trains[i].arr[1],trains[i].troncons[1:]))

    final_events = copy.deepcopy(events)
    histo_aiguillages = {"9": [], "10": [], "11": [], "12": [], "13": []}
    switch_init = {"9": ("d",True), "10": ("d",True), "11": ("d",True), "12": ("d",True), "13": ("d",True)} 

    for i in range(len(events)):
        for j in range(len(events[i])):
            if len(events[i][j]) > 0:
                final_events[i][j] = []
                for order in events[i][j]:
                    histo_aiguillages[order[1]].append((order[2], i, j))
                    switch_init[order[1]] = (order[2], False) # met à jour l'état de l'aiguillage

    sillon = Trajet(trains, final_events)
    sillon.histo_switch = histo_aiguillages
    sillon.switch_init = switch_init

    for train in sillon.trains:
        sillon.wait_list.append((train.id, train.dep[0], train.dep[0], 1)) # ajoute le train à la liste d'attente
        sillon.events[train.id][0].append(("incr", int(train.dep[0])))
    sillon.posInitial = start
    sillon.posFinal = end
    return sillon


def build_token(o1):
    tokens = [0]*9 #un token par canton
    offset = [0]*len(o1.trains) #offset pour les trains
    wait_list = []
    train_list = [x for x in range(len(o1.trains))]
    run_events = copy.deepcopy(o1.events)

    while len(train_list) > 0: #Possible d'optimiser largement -> pas besoin de suivre l'execution, juste compter les incr
        current = train_list.pop(0)
        flag = False
        i = 0
        offset_tmp = 0
        cpy_events = copy.deepcopy(run_events[current])
        while i < len(run_events[current]) and not flag:
            event = cpy_events.pop(0)
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
                    elif order[0] == "auth": 
                        continue
                    elif order[0] == "turn":
                        continue
            offset_tmp += 1
            i += 1
            if flag:
                offset[current] += offset_tmp
        run_events[current] = cpy_events
    return tokens


def build_troncons(trains):
    troncons = []
    for train in trains:
        troncons.append([])
        troncons[train.id].append(int(train.dep[0]))
        for prog in train.prog:
            for tro in prog[2]:
                if troncons[train.id][-1] != tro:
                    troncons[train.id].append(tro)
    return troncons


def findCritical(t1, troncons_o1, t2, troncons_o2, o1):
    crit = []

    for i in range(len(troncons_o2[t2.id])):
        endT1 = t1.last_crit[t2.id]
        for j in range(len(troncons_o1[t1.id])-1, endT1-1, -1):
            if troncons_o2[t2.id][i] == troncons_o1[t1.id][j]:
                crit.append(troncons_o2[t2.id][i])
                t1.last_crit[t2.id] = j
                t2.last_crit[t1.id] = i
                break
    return crit



def last_index(lst, value):
    """Retourne le dernier index de value dans lst, ou -1 si value n'est pas dans lst."""
    for i in range(len(lst)-1, -1, -1):
        if lst[i] == value:
            return i
    return -1

def search_prec_histo(histo, switch, train, numEv):
    for i in range(len(histo[switch])-1):
        if histo[switch][i+1][1] == train and histo[switch][i+1][2] == numEv:
            return histo[switch][i]


def compose(o1,o2,save=False):
    tokens_o1 = build_token(o1)
    histo_o1 = o1.histo_switch
    histo_o2 = o2.histo_switch

    troncons_o1 = build_troncons(o1.trains)
    troncons_o2 = build_troncons(o2.trains)

    #supprime les att du début dans o2
    for i in range(len(o2.trains)):
        o2.events[i][0] = []

    #simplifier les turns
    for aig, hist in histo_o2.items():
        for i in range(len(hist)):
            if len(histo_o1[aig]) > 0: #init
                if histo_o1[aig][-1][0] != hist[i][0]: #different
                    train = hist[i][1]
                    event = hist[i][2]
                    o2.events[train][event].append(("turn", aig, hist[i][0]))
            else: #pas d'init
                o1.switch_init[aig] = (histo_o2[aig][i][0], False) #met à jour l'état de l'aiguillage

    #fusionne les historiques
    histo_o3 = copy.deepcopy(histo_o1)
    for aig, hist in histo_o2.items():
        if aig in histo_o3:
            for init in hist:
                histo_o3[aig].append((init[0], init[1], init[2]+len(o1.events[init[1]])-1))
        else:
            histo_o3[aig] = hist

    #gère les ressources critiques
    for i in range(len(o1.trains)):
        for j in range(len(o2.trains)):
            if i != j:
                for t in range(len(troncons_o2[j])):
                    if troncons_o2[j][t] in troncons_o1[i]:
                        index_incr = last_index(troncons_o1[i], troncons_o2[j][t])+1
                        index_att = t-1
                        sec_crit = troncons_o2[j][t]
                        tokens_o1[int(sec_crit)] += 1
                        o1.events[i][index_incr].append(("incr", sec_crit))
                        o2.events[j][index_att].append(("att", sec_crit, tokens_o1[int(sec_crit)]))
                        if len(o2.events[j][index_att]) != 0:
                            cpy_events = copy.deepcopy(o2.events[j][index_att])
                            for order in cpy_events:
                                if order[0] == "turn":
                                    prec = search_prec_histo(histo_o3, order[1], j, index_att+len(o1.events[j])-1)
                                    if prec is not None:
                                        _, train, event = prec
                                        event += 1
                                    else:
                                        train = i
                                        event = index_incr
                                    o1.events[train][event].append(("turn", order[1], order[2]))
                                    o2.events[j][index_att].remove(order)
                                    #histo_o3[order[1]][-1] = (order[2], train, event+1) #met à jour l'historique
    

    #ajout des auth
    for e in range(len(o2.trains)):
        for n in range(len(o2.events[e])):
            for o in range(len(o2.events[e][n])):
                if o2.events[e][n][o][0] == "turn":
                    o2.events[e][n].append(["auth"])
    
    for t in range(len(o2.trains)):
        o2.events[t][0].append(["auth"])


    #fusion des événements
    o3_events = copy.deepcopy(o1.events)
    for i in range(len(o2.trains)):
        o3_events[i][-1] += o2.events[i][0]
        o3_events[i] += o2.events[i][1:]
    
    #fusion des trains
    o3_trains = copy.deepcopy(o1.trains)
    for t in range(len(o2.trains)):
        o3_trains[t].prog += o2.trains[t].prog
        o3_trains[t].arr = o2.trains[t].arr
    
    o3 = Trajet(o3_trains, o3_events)
    o3.switch_init = o1.switch_init
    o3.histo_switch = histo_o3
    o3.wait_list = o1.wait_list
    o3.posInitial = o1.posInitial
    o3.posFinal = o2.posFinal
    
    optimisation(o3)
    if save:
        filename = f"model/pickle/{o3.posInitial.replace('*', 'o')}-{o3.posFinal.replace('*', 'o')}.pkl"
        with open(filename, "wb") as file:
            file.write(pickle.dumps(o3))
    return o3


def majTokens(o1, token, value):
    for t in range(len(o1.trains)):
        for e in range(len(o1.events[t])):
            for o in range(len(o1.events[t][e])):
                if o1.events[t][e][o][0] == "att" and o1.events[t][e][o][1] == token:
                    if o1.events[t][e][o][2] > value:
                        o1.events[t][e][o] = ("att", token, value-1)                         


def optimisation(o1):
    #reduire les programmes des trains
    for i in range(len(o1.trains)):
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
    
    #supprimer les doublons
    """ for t in range(len(o1.trains)):
        for e in range(len(o1.events[t])):
            orders_cpy = copy.deepcopy(o1.events[t][e])
            rmv = []
            for o in range(len(o1.events[t][e])):
                if o1.events[t][e][o][0] == "att":
                    for p in range(len(o1.events[t][e])):
                        if o != p and o1.events[t][e][p][0] == "att" and o1.events[t][e][p][1] == o1.events[t][e][o][1]:
                            orders_cpy.remove(o1.events[t][e][p])
                            majTokens(o1, o1.events[t][e][p][1], o1.events[t][e][p][2])
                if o1.events[t][e][o][0] == "incr":
                    for p in range(len(o1.events[t][e])):
                        if o != p and o1.events[t][e][p][0] == "incr" and o1.events[t][e][p][1] == o1.events[t][e][o][1]:
                            rmv.append(o1.events[t][e][p])
            for elem in rmv:
                orders_cpy.remove(elem)
            o1.events[t][e] = orders_cpy """


import subprocess


def verifTMP(e1,e2, e3):
    s6 = etats[f"{e2} -> {e3}"].split("__")
    o6 = createProgram(e2, e3, s6)
    #print(f"o6\n{o6}")
    #o7 = compose(o5, o6)

    with open(f"model/pickle/{e1.replace("*","o")}-{e2.replace("*","o")}.pkl", "rb") as file:
        tmp = file.read()
        saved = pickle.loads(tmp)
    #print(f"saved\n{saved}")
    o7 = compose(saved, o6)
    
    #print(f"o7\n{o7}")
    #print(f"o7 switch historique : {o7.histo_switch}")

    with open("model/composition.tla", "w") as file:
        file.write(trajet2model(o7, build_troncons(o7.trains)))

    command = ["java", "-jar", f"model/tla2tools.jar", "-config", f"model/compo.cfg", f"model/model2.tla"]
    f = open(f"model/out.log", "w")
    p = subprocess.Popen(command, stdout=f, stderr=f)
    p.wait()
    f.close()


if __name__ == "__main__":

    etats = dict()
    with open("etat_elem.json", "r") as file:
        etats = json.load(file)

    s4_1 = etats["N4L5R2* -> N8L7R2*"].split("__")
    o1 = createProgram("N4L5R2*", "N8L7R2*",s4_1) 
    s4_2 = etats["N8L7R2* -> N8*4R2*"].split("__")
    o2 = createProgram("N8L7R2*", "N8*4R2*",s4_2)
    print(f"o1\n{o1}")
    print(f"o2\n{o2}")
    o3 = compose(o1, o2)
    print(f"\no3\n{o3}")

    """s5 = etats["N8*4R2* -> N8R4*2*"].split("__")
    o4 = createProgram("N8*4R2*", "N8R4*2*", s5)
    print(f"o4\n{o4}")
    o5 = compose(o3, o4)
    print(f"o5\n{o5}")
    print(f"o5 switch historique : {o5.histo_switch}")
    """

    
    """ cpt = 0
    with open("allErrors.log", "r") as file:
        for line in file:
            cpt += 1
            chemin = re.findall(r"N(?:[1-8][LR\*]){3} -> N(?:[1-8][LR\*]){3} -> N(?:[1-8][LR\*]){3}", line)[0]
            
            #state =  "N5R8R4R -> N3R2*6* -> N1R2*6*"
            e = chemin.split(" -> ")
            verifTMP(e[0], e[1], e[2]) """


    """ s6 = etats["N2*8*7R -> N2*8*6R"].split("__")
    o6 = createProgram("N2*8*7R", "N2*8*6R", s6)
    print(f"o6\n{o6}")
    #o7 = compose(o5, o6)

    with open(f"model/pickle/N5R8R4R-N2o8o7R.pkl", "rb") as file:
        tmp = file.read()
        saved = pickle.loads(tmp)
    print(f"saved\n{saved}")
    o7 = compose(saved, o6)
    
    print(f"o7\n{o7}")
    print(f"o7 switch historique : {o7.histo_switch}")

    with open("model/composition.tla", "w") as file:
        file.write(trajet2model(o7, build_troncons(o7.trains))) """