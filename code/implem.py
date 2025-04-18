import inferrule as ir
from inspect import signature
from copy import deepcopy
import json
import subprocess


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

class Simulation:
    def __init__(self, circuit, trains, regulateur, rules):
        self.circuit = circuit
        self.baseState = Etat(trains, regulateur)
        self.rules = rules
        self.world = {}
        self.queue = []

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
        
        while self.queue:
            currentState = self.queue.pop(0)
            for train in currentState.gamma.values():
                for rule in self.rules:
                    if not currentState.isBot:                
                        etatPrime = self.infer(currentState, rule, train.id)
                        if etatPrime:
                            if etatPrime not in self.queue:
                                self.queue.append(etatPrime)

                            if str(etatPrime) not in self.world:
                                self.world[str(etatPrime)] = {}
                            self.world[str(currentState)][str(etatPrime)] = f"{rule.__name__} on {train.id}"

        return True
    

    def translateDOT(self, name="world"):
        #Convertir le dictionnaire en format DOT
        dot = "digraph {\n"
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
                            

def loadScenar(gamma, reg, nom):
    sim = Simulation(reg.circuit, gamma, reg, regles)
    #print(sim.baseState)
    flag = sim.startSim()

    if flag:
        print("Simulation terminée")
        sim.export("graph/"+nom)
        sim.translateDOT("graph/"+nom)
    else :
        print("Simulation échouée")


        
## Scénario 1 : Good Ending
def scenar1(name="goodEnding"):
    circuit = {
        "0R" : 1,
        "1R" : 2,
        "1L" : 0,
        "2L" : 1,
        "3L" : 1
    }
    reg = ir.Regul(4, [2,3], circuit)
    car = ir.Train(0,0,["Start(R)","Until(2)","Stop()"])
    tri = ir.Train(1,3,["Start(L)","Until(0)","Stop()"])

    Gamma = dict()
    Gamma[0] = car
    Gamma[1] = tri
    

    reg.addEv(0,2,["incr(1)"])
    reg.addEv(1,3,["att(1,1)"])

    return Gamma, reg, name


### Scénario 2 : Deadlock
def scenar2(name="deadlock"):
    circuit = {
        "0R" : 1,
        "1R" : 2,
        "1L" : 0,
        "2R" : 3,
        "2L" : 1,
        "3L" : 2,
        "4L" : 2,
    }

    reg = ir.Regul(5, [1,2], circuit)
    car = ir.Train(0,0,["Start(R)","Until(3)","Stop()"])
    tri = ir.Train(1,4,["Start(L)","Until(0)","Stop()"])

    Gamma = dict()
    Gamma[0] = car
    Gamma[1] = tri
    

    reg.addEv(0,1,["att(2,1)"])
    reg.addEv(0,2,["incr(1)"])
    
    reg.addEv(1,2,["att(1,1)"])
    reg.addEv(1,1,["incr(2)"])


    return Gamma, reg, name


## Scénario 3 : Collision
def scenar3(name="collision"):
    circuit = {
        "0R" : 1,
        "1R" : 2,
        "1L" : 0,
        "2R" : 3,
        "2L" : 1,
        "3L" : 2
    }

    reg = ir.Regul(3, [3,0], circuit)
    car = ir.Train(0,0,["Start(R)","Until(3)","Stop()"])
    tri = ir.Train(1,3,["Start(L)","Until(0)","Stop()"])

    Gamma = dict()
    Gamma[0] = car
    Gamma[1] = tri

    return Gamma, reg, name

 
### Main 


regles = [ir.crash, ir.start, ir.until, ir.until_cons, ir.until_ev ,ir.until_cons_ev, ir.wait, ir.stop]

loadScenar(*scenar3("collisionV2"))