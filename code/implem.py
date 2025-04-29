import inferrule as ir
from inspect import signature
from copy import deepcopy
import json
import subprocess
import time
import re


### Classes


class Etat:
    def __init__(self, trains, regulateur):
        self.gamma = trains
        self.reg = regulateur
        self.isBot = False
    
    def __str__(self):
        s = ""
        if self.reg:
            for id, train in self.gamma.items():
                s += f"Train {id} : {train}\n"
            s += f"Regulateur : {self.reg}"
        else:
            s += "Bottom"
        return s
    
    def isCollision(self):
        for train in self.gamma.values():
            for other in self.gamma.values():
                if train.id != other.id and train.pos == other.pos:
                    return True
        return False

class Simulation:
    def __init__(self, circuit, trains, regulateur, rules):
        self.circuit = circuit
        self.baseState = Etat(trains, regulateur)
        self.rules = rules
        self.world = {} # graphe d'intéraction
        self.parents = {} # graphe enfant : parents
        self.states = {} # Dictionnaire des états
        self.queue = []
        self.collision = False
        self.deadlock = False
        self.objectifs = [] # position sur lesquels on veut que les trains s'arrêtent

    def __str__(self):
        return "Pas implémenté"    # Voir comment le représenter

    """ 
    Applique une règle d'inférence sur le train id depuis un état donné
    In: état
    out: état'
    """
    def infer(self, etatB, rule, id):
        #Copie l'état avant
        etat = deepcopy(etatB)
        t = etat.gamma[id]
        sign = signature(rule)
        res = False


        if len(sign.parameters) == 1:
            res = rule(t)
        elif len(sign.parameters) == 2:
            if rule.__name__ == "crash":
                for train in etat.gamma.values():
                    res = rule(t, train)
                    if res:
                        etat.isBot = True
                        etat.reg = ""
                        etatB.isBot = True
                        break
            else:
                res = rule(t, etat.reg)
        elif len(sign.parameters) == 3:
            res = rule(t, etat.reg, etat.gamma)
        else:
            raise Exception("Erreur dans la signature de la règle d'inférence")
        
        return etat if res else None
        
    def startSim(self):
        self.queue.append(self.baseState)
        self.world[str(self.baseState)] = {}
        self.parents[str(self.baseState)] = {""}

        while self.queue:
            currentState = self.queue.pop(0)
            for train in currentState.gamma.values():
                for rule in self.rules:
                    if not currentState.isBot:                
                        etatPrime = self.infer(currentState, rule, train.id)
                        if etatPrime:
                            if str(etatPrime) not in self.world:
                                self.queue.append(etatPrime)
                                if etatPrime.isCollision():
                                    self.collision = True
                                    self.states[str(etatPrime)] = "red"
                                    
                                self.world[str(etatPrime)] = {}
                                self.parents[str(etatPrime)] = {}
                            self.world[str(currentState)][str(etatPrime)] = f"{rule.__name__} on {train.id}"
                            self.parents[str(etatPrime)][str(currentState)] = f"{rule.__name__} on {train.id}"

        return True
    

    def search_deadlock(self):
        for etat, value in self.world.items():
            empty = True
            dl = False
            regex = r"Train [0-9]+ : [0-9]+/[L,R,*] : \[\]"
            if value == {}:
                line = etat.split("\n")
                nbTrain = re.findall("Train",etat)
                for i in range(len(nbTrain)):
                    if not re.search(regex, line[i]):
                        empty = False
                        dl = True
                        self.deadlock = True
                    else:
                        pos_final = re.findall(r"[0-9]+/[L,R,*]", line[i])[0]
                        if pos_final != self.objectifs[i]:
                            dl = True
                            self.deadlock = True
            if dl:
                if empty:
                    self.states[str(etat)] = "blue"
                else:
                    self.states[str(etat)] = "yellow"


    def blacklist(self):
        """
        Renvoi les états à ne pas afficher dans le graphe
        """
        blacklist = []
        pile = [str(self.baseState)]
        while pile:
            current = pile.pop(0)
            if current not in blacklist:
                suppr = True
                for parent in self.parents[current]:
                    if parent not in blacklist and parent not in self.states:
                        suppr = False
                        break
                if suppr: #Si tous les parents sont dans la blacklists ou possèdent un statut
                    blacklist.append(current)
            for child in self.world[current]:
                if child not in pile:
                    pile.append(child)
        return set(blacklist)

    
    #Convertir le dictionnaire en format DOT
    def translateDOT(self, name="world"):
        #chercher des blocages
        self.search_deadlock()

        blacklist = self.blacklist()
        dot = "digraph {\nnode [style = filled]\n"

        for state, color in self.states.items():
            if state not in blacklist:
                if color == "red":
                    dot += f'    "{state}" [fillcolor="#ff4747"];\n'
                elif color == "yellow":
                    dot += f'    "{state}" [fillcolor="yellow"];\n'
                elif color == "blue":
                    dot += f'    "{state}" [fillcolor="blue"];\n'



        for base, value in self.world.items():
            #si l'état n'est pas un satut (crash ou deadlock)
            if base not in blacklist and base not in self.states:
                for prime, rule in value.items():
                    dot += f'    "{base}" -> "{prime}" [label="{rule}"];\n'

        dot += "}"   
        #Enregistrer le fichier DOT
        with open(name+".dot", "w") as file:
            file.write(dot)
            subprocess.run(["dot", "-Tsvg", name+".dot", "-o", name+".svg"])
        
        coolPaths = self.interestingPaths(blacklist)
        with open(name+"_coolPaths.dot", "w") as file:
            file.write(coolPaths)
            subprocess.run(["dot", "-Tsvg", name+"_coolPaths.dot", "-o", name+"_coolPaths.svg"])


    def interestingPaths(self, blacklist):
        """
        Renvoi les chemins intéressants
        """        
        selected = [""]*4
        for node, children in self.world.items():
            if node not in blacklist:
                if node in self.states:
                    color = self.states[node]
                    if color == "red" and not selected[1]:
                        selected[1] = (node, "red")
                    elif color == "yellow" and not selected[2]:
                        selected[2] = (node,"yellow")
                    elif color == "blue" and not selected[3]:
                        selected[3] = (node,"blue")
                else:
                    if children == {}:
                        selected[0] = (node,None)

        path = "digraph {\nnode [style = filled]\n"
        for i in range(4):
            if selected[i]:
                node, color = selected[i]
                if color == "red":
                    path += f'    "{node}" [fillcolor="#ff4747"];\n'
                elif color == "yellow":
                    path += f'    "{node}" [fillcolor="yellow"];\n'
                elif color == "blue":
                    path += f'    "{node}" [fillcolor="blue"];\n'
                
                current = node
                while current != None:
                    for parent, rule in self.parents[current].items():
                        if parent not in self.states:
                            s = f'    "{parent}" -> "{current}" [label="{rule}"];\n'
                            if s not in path:
                                path += s

                            if parent != str(self.baseState):
                                current = parent
                            else:
                                current = None
                            break
        return path + "}"


    def translateDOT_legacy(self, name="world"):
        #chercher des blocages
        self.search_deadlock()

        #Convertir le dictionnaire en format DOT
        dot = "digraph {\nnode [style = filled]\n"

        for state, color in self.states.items():
            if color == "red":
                dot += f'    "{state}" [fillcolor="#ff4747"];\n'
            elif color == "yellow":
                dot += f'    "{state}" [fillcolor="yellow"];\n'
            elif color == "blue":
                dot += f'    "{state}" [fillcolor="blue"];\n'

        for base, value in self.world.items():
            for prime, rule in value.items():
                dot += f'    "{base}" -> "{prime}" [label="{rule}"];\n'
        dot += "}"
        #Enregistrer le fichier DOT
        with open(name+".dot", "w") as file:
            file.write(dot)
            subprocess.run(["dot", "-Tsvg", name+".dot", "-o", name+".svg"])


    def export(self, name="world"):
        with open(name+".json", "w") as file:
            json.dump(self.world, file, indent=4)






### Scenario manager
                            





def loadScenar(gamma, reg, objectif, nom):
    print(f"#### Scénario {nom} chargé ####\n")
    sim = Simulation(reg.circuit, gamma, reg, regles)
    sim.objectifs = objectif

    #print(sim.baseState)
    t_start = time.time()
    flag = sim.startSim()

    if not flag:
        print(f"Simulation échouée : {time.time()-t_start:.3f}s")
        return False

    print(f"Simulation terminée en  {time.time()-t_start:.3f}s")
    sim.export("graph/"+nom)

    t_start = time.time()
    sim.translateDOT("graph/"+nom)
    sim.translateDOT_legacy("graph/"+nom+"_legacy")
    print(f"Graphe généré en {time.time()-t_start:.3f}s")
    
    if sim.collision:
        print("Warning : Collision détectée")

    if sim.deadlock:
        print("Warning : Destination non atteinte")

        
## Scénario 1 : Good Ending
def scenar1(name="goodEnding"):
    circuit = {
        "0R" : {1:None},
        "1R" : {2:[(0,"d")], 3:[(0,"v")]},
        "1L" : {0:None},
        "2L" : {1:[(0,"d")]},
        "3L" : {1:[(0,"v")]},
    }

    aig = ["d"]

    reg = ir.Regul(4, [2,0], circuit, aig)
    car = ir.Train(0,0,["StartUntil(R,2)"])
    tri = ir.Train(1,3,["StartUntil(L,0)"])

    Gamma = dict()
    Gamma[0] = car
    Gamma[1] = tri
    
    # addEv(train, numéro d'event, [event])
    reg.addEv(0,2,["turn(0,v)","incr(1)"])
    reg.addEv(1,0,["att(1,1)"])
    reg.addEv(1,2,[])

    reg.nbEv[0] = 3
    reg.nbEv[1] = 3

    objectif = ["2/*", "0/*"]

    return Gamma, reg, objectif, name


### Scénario 2 : Deadlock
def scenar2(name="deadlock"):
    circuit = {
        "0R" : {1 : None},
        "1R" : {2 : None},
        "1L" : {0 : None},
        "2R" : {3 : [(0,"d")], 4 : [(0,"v")]},
        "2L" : {1 : None},
        "3L" : {2 : [(0,"d")]},
        "4L" : {2 : [(0,"v")]},
    }

    aig = [("d",0)]

    reg = ir.Regul(5, [3,4], circuit, aig)
    car = ir.Train(0,0,["StartUntil(R,3)"])
    tri = ir.Train(1,4,["StartUntil(L,0)"])

    Gamma = dict()
    Gamma[0] = car
    Gamma[1] = tri
    
    reg.addEv(0,3,["incr(3)"])
    reg.addEv(1,4,["att(3,1)"])

    objectif = ["3/*", "0/*"]
    
    return Gamma, reg, objectif, name


## Scénario 3 : Collision
def scenar3(name="collision"):
    circuit = {
        "9R" : {0 : None},
        "0L" : {9 : None},
        "0R" : {2 : [(0,"d")]},
        "1R" : {2 : [(0,"v")]},
        "2R" : {3 : [(1,"d")], 4 : [(1,"v")]},
        "2L" : {0 : [(0,"d")], 1 : [(0,"v")]},
        "3L" : {2 : [(1,"d")]},
        "4L" : {2 : [(1,"v")]},
        "4R" : {5 : None},
        "5L" : {4 : None}
    }

    aig = ["v", "v"]

    reg = ir.Regul(5, [4,3], circuit, aig)

    reg.addEv(0,1,["turn(0,d)"])
    reg.addEv(0,2,["turn(1,d)"])
    reg.addEv(1,1,["turn(1,v)"])
    reg.addEv(1,2,["turn(0,v)"])

    gamma = {
        0: ir.Train(0,9,["StartUntil(R,3)"]),
        1: ir.Train(1,5,["StartUntil(L,1)"]),
    }

    reg.nbEv[0] = 4
    reg.nbEv[1] = 4

    objectif = ["3/*", "1/*"]

    return gamma, reg, objectif, name

## Scénario 4 : Maquette
def scenar4(name="maquette"):
    graph = {
        '0L' : {2: [(0,"d"), (1,"v")]},

        '1L' : {2: [(0,"v"), (1,"v")]},

        '2L' : {6: [(2,"d")], 7: [(2,"v")]},
        '2R' : {3: [(1,"d")], 0: [(0,"d"), (1,"v")], 1: [(0,"v"), (1,"v")]},

        '3L' : {2:  [(1,"d")]},
        '3R' : {4: [(4,"d")], 6: [(4,"v")]},

        '4L' : {3: [(4,"d")]},
        '4R' : {6: [(3,"d")]},

        '5L' : {3: [(4,"v")]},
        '5R' : {6: [(3,"v")]},

        '6L' : {4: [(3,"d")], 6: [(3,"v")]},
        '6R' : {2: [(2,"d")]},

        '7R' : {2: [(2,"v")]}
    }

    aig = ["d", "d", "v", "d", "d"]

    reg = ir.Regul(8, [2,1], graph, aig)

    #reg.addEv(0,0,[])
    #reg.addEv(0,1,[])
    reg.addEv(0,2,["turn(2,d)","turn(1,d)","incr(2)", "att(2,2)"])
    reg.addEv(0,3,["turn(2,d)","incr(6)"])
    reg.addEv(0,4,["incr(2)"])

    #reg.addEv(1,0,[])
    reg.addEv(1,1,["att(2,1)"])
    #reg.addEv(1,2,[])
    reg.addEv(1,3,["turn(2,v)","incr(2)", "att(2,3)"])
    reg.addEv(1,4,[])

    reg.nbEv[0] = 5
    reg.nbEv[1] = 5

    Gamma = {
        0: ir.Train(0,3,["StartUntil(L,7)","StartUntil(R,2)","StartUntil(L,6)"]),
        1: ir.Train(1,4,["StartUntil(R,3)","StartUntil(L,2)"]),
    }

    objectif = ["6/*", "2/*"]

    return Gamma, reg, objectif, name

def scenar5(name="wrongWay"):
    circuit = {
        "0R" : {2 : [(0,"d")]},
        "1R" : {2 : [(0,"v")]},
        "2R" : {3 : [(1,"d")], 4 : [(1,"v")]},
        "2L" : {0 : [(0,"d")], 1 : [(0,"v")]},
        "3L" : {2 : [(1,"d")]},
        "4L" : {2 : [(1,"v")]}
    }

    aig = ["v", "v"]

    reg = ir.Regul(5, [0,1], circuit, aig)

    reg.addEv(0,0,["att(2,1)"])
    reg.addEv(1,1,["turn(0,d)","incr(2)"])

    gamma = {
        0: ir.Train(0,0,["Start(R)","Until(3)","Stop()"]),
        1: ir.Train(1,4,["Start(L)","Until(1)","Stop()"]),
    }

    objectif = ["3/*", "1/*"]

    return gamma, reg, objectif, name

"""
Contexte : pour ce scénario, on imagine que le trajet du train 1 doit être 6 -> 4 -> 3
Cependant, il prend le chemin 6 -> 5 -> 3
"""
def scenar6(name="wrongWayButOk"):
    graph = {
        '0L' : {2: [(0,"d"), (1,"v")]},

        '1L' : {2: [(0,"v"), (1,"v")]},

        '2L' : {6: [(2,"d")], 7: [(2,"v")]},
        '2R' : {3: [(1,"d")], 0: [(0,"d"), (1,"v")], 1: [(0,"v"), (1,"v")]},

        '3L' : {2:  [(1,"d")]},
        '3R' : {4: [(4,"d")], 6: [(4,"v")]},

        '4L' : {3: [(4,"d")]},
        '4R' : {6: [(3,"d")]},

        '5L' : {3: [(4,"v")]},
        '5R' : {6: [(3,"v")]},

        '6L' : {4: [(3,"d")], 5: [(3,"v")]},
        '6R' : {2: [(2,"d")]},

        '7R' : {2: [(2,"v")]}
    }

    aig = ["d", "v", "v", "v", "v"]

    reg = ir.Regul(8, [7,3], graph, aig)


    Gamma = {
        0: ir.Train(0,0,["Start(L)","Until(7)","Stop()"]),
        1: ir.Train(1,6,["Start(L)","Until(3)","Stop()"]),
    }

    objectif = ["7/*", "3/*"]

    return Gamma, reg, objectif, name

## Scénario 7 : Threesome
def scenar7(name="threesome"):
    circuit = {
        "9R" : {0 : None},
        "0L" : {9 : None},
        "0R" : {2 : [(0,"d")]},
        "1R" : {2 : [(0,"v")]},
        "2R" : {3 : [(1,"d")], 4 : [(1,"v")]},
        "2L" : {0 : [(0,"d")], 1 : [(0,"v")]},
        "3L" : {2 : [(1,"d")]},
        "4L" : {2 : [(1,"v")]},
        "4R" : {5 : None},
        "5L" : {4 : None}
    }

    aig = ["v", "v"]

    reg = ir.Regul(5, [3,3,3], circuit, aig)

    reg.addEv(0,1,["turn(0,d)"])
    reg.addEv(0,2,["turn(1,d)"])
    reg.addEv(1,1,["turn(1,v)"])
    reg.addEv(1,2,["turn(0,v)"])

    reg.addEv(0,3,[])
    reg.addEv(1,3,[])
    reg.addEv(2,3,[])

    reg.nbEv[0] = 4
    reg.nbEv[1] = 4
    reg.nbEv[2] = 4

    gamma = {
        0: ir.Train(0,9,["StartUntil(R,3)"]),
        1: ir.Train(1,5,["StartUntil(L,1)"]),
        2: ir.Train(2,3,["StartUntil(L,9)"]),
    }

    objectif = ["3/*", "1/*", "9/*"]

    return gamma, reg, objectif, name


def scenar8(name="atomic"):
    circuit = {
        "0L" : {1:None},
        "1R" : {0:None},
        "1L" : {3:[(0,"d")]},
        "2L" : {3:[(0,"v")]},
        "3R" : {1:[(0,"d")], 2:[(0,"v")]},
        "3L" : {4:[(1,"d")], 5:[(1,"v")]},
        "4R" : {3:[(1,"d")]},
        "4L" : {6:[(2,"d")]},
        "5R" : {3:[(1,"v")]},
        "5L" : {6:[(2,"v")]},
        "6R" : {4:[(2,"d")], 5:[(2,"v")]},
        "6L" : {7:[(3,"d")], 8:[(3,"v")]},
        "7R" : {6:[(3,"d")]},
        "8R" : {6:[(3,"v")]}
    }

    aig = ["v","v","v","v"]

    reg = ir.Regul(9, [1,4], circuit, aig)

    reg.addEv(0,1,["att(3,1)"])
    reg.addEv(0,3,["att(6,1)"])

    reg.addEv(1,2,["turn(0,d)","turn(1,d)", "incr(3)"])
    reg.addEv(1,4,["turn(2,d)", "turn(3,d)", "incr(6)"])

    Gamma = {
        0: ir.Train(0,0,["StartUntil(L,7)"]),
        1: ir.Train(1,2,["StartUntil(L,8)"])
    }

    reg.nbEv[0] = 6
    reg.nbEv[1] = 5

    return Gamma, reg, ["7/*", "8/*"], name

"""
Problème d'aiguillage dans l'état initial
"""
def miniscenar1(name="crashSwitch"):
    circuit = {
        "0R" : {1:None},
        "1R" : {2:[(0,"d")], 3:[(0,"v")]},
        "1L" : {0:None},
        "2L" : {1:[(0,"d")]},
        "3L" : {1:[(0,"v")]},
    }

    aig = ["v"]

    reg = ir.Regul(4, [2,3], circuit, aig)

    reg.addEv(0,2,["turn(0,v)","incr(1)"])
    reg.addEv(1,3,["att(1,1)"])

    Gamma = {
        0: ir.Train(0,0,["StartUntil(R,2)"]),
        1: ir.Train(1,3,["StartUntil(L,0)"]),
    }

    return Gamma, reg, ["2/*", "0/*"], name


"""
Les deux trains attendent
"""
def miniscenar2(name="deadlockWait"):
    circuit = {
        "0R" : {1:None},
        "1R" : {2:[(0,"d")], 3:[(0,"v")]},
        "1L" : {0:None},
        "2L" : {1:[(0,"d")]},
        "3L" : {1:[(0,"v")]},
    }

    aig = ["d"]

    reg = ir.Regul(4, [0,3], circuit, aig)

    reg.addEv(0,0,["att(1,1)"])
    reg.addEv(1,3,["att(1,1)"])

    Gamma = {
        0: ir.Train(0,0,["Start(R)","Until(2)","Stop()"]),
        1: ir.Train(1,3,["Start(L)","Until(0)","Stop()"]),
    }

    return Gamma, reg, ["2/*", "0/*"], name


"""
Problème dans le 'code' du train
"""
def miniscenar3(name="deadlockTrain"):
    circuit = {
        "0R" : {1:None},
        "1L" : {0:None},
        "1R" : {2:None},
        "2L" : {1:None}
    }

    reg = ir.Regul(3, [1], circuit, [])

    Gamma = {
        0: ir.Train(0,0,["StartUntil(R,1)"])
    }

    return Gamma, reg, ["2/*"], name


"""
Problème dans le 'code' du régulateur
"""
def miniscenar4(name="deadlockRegulateur"):
    circuit = {
        "0R" : {1:None},
        "1L" : {0:None},
        "1R" : {2:None},
        "2L" : {1:None}
    }

    reg = ir.Regul(3, [2], circuit, [])

    reg.addEv(0,1,["att(2,1)"])

    Gamma = {
        0: ir.Train(0,0,["Start(R)","Until(2)","Stop()"])
    }

    return Gamma, reg, ["2/*"], name



### Main 



if __name__ == "__main__":  
    regles = [ir.start, ir.stop, ir.until ,ir.until_cons, ir.incr_af, ir.incr_bf, ir.att_af, ir.att_bf, ir.turn, ir.elimEv]
    loadScenar(*miniscenar1())