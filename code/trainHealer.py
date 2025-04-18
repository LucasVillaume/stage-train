import inferrule as ir


class Bob:
    def __init__(self, gamma, reg, objectifs, problem):
        self.gamma = gamma
        self.reg = reg
        self.objectif = objectifs
        self.problem = problem


    def findProblem(self):
        if self.problem == "deadlock":
            return self.deadlock()
        elif self.problem == "crash":
            return self.crash()
        else:
            print("Unknown problem type. Use 'deadlock' or 'crash'.")
    
    def deadlock(self):
        #liste des deadlocks
        deadlocks = []
        for train in self.gamma.values():
            pb = ""
            #ordre vide
            if train.nextProg() is None:
                if self.objectif[train.id] != train.pos:
                    pb += f"train {str(train.id)} : mauvais until"
                    if train.pos == self.reg.auths[train.id]:
                        pb += " et mauvaise autorisation"
            #ordre non-vide
            else:
                #train bloqué par auths
                if train.pos == self.reg.auths[train.id]:
                    for ev, w_train in self.reg.waiting.items():
                        if w_train == train.id:
                            pb += f"train {str(train.id)} : le token {str(ev[0])} n'atteint jamais la valeur {str(ev[1])}, il faut revoir les évènements"
                    #Ce n'est pas un problème de wait
                    if pb == "": 
                        pb += f"train {str(train.id)} : mauvaise autorisation, le train est bloqué"
                #ordre non-vide et pas bloqué par auths
                else:
                    if ir.suivant(train.pos, train.dir, self.reg) is None:
                        posDir = str(train.pos) + train.dir
                        if posDir in self.reg.circuit and self.reg.circuit[posDir] != {}:
                            pb += f"train {str(train.id)} : problème d'aiguillage, le train est bloqué en {posDir}"
                        else:
                            pb += f"train {str(train.id)} : mauvaise direction OU problème d'aiguillage, le train à pris le mauvais chemin"
            deadlocks.append(pb)
        return deadlocks


if __name__ == "__main__":
    # Exemple d'utilisation
    circuit = {
        "0R" : {1:None},
        "1R" : {2:[(0,"d")], 3:[(0,"v")]},
        "1L" : {0:None},
        "2L" : {1:[(0,"d")]},
        "3L" : {1:[(0,"v")]},
    }

    aig = ["v"]

    reg = ir.Regul(4, [2,3], circuit, aig)

    reg.addEv(0,3,["turn(0,v)","incr(1)"])
    reg.addWait(1,1,1)

    t0 = ir.Train(0,3,["Until(2)","Stop()"])
    t0.dir = "R"
    t1 = ir.Train(1,3,["Until(0)","Stop()"])
    t1.dir = "L"

    gamma = {
        0: t0,
        1: t1
    }

    objectifs = [2]
    problem = "deadlock"

    bob = Bob(gamma, reg, objectifs, problem)
    print(bob.findProblem())
