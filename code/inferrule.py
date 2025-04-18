
class Regul:
    def __init__(self, nbJ, auths, circuit, aiguille):
        self.jetons = [0]*nbJ
        self.auths = auths
        self.ev = dict()
        self.nbEv = [0]*len(auths)
        self.nextEventNum = [0]*len(auths)
        self.waiting = dict()
        self.circuit = circuit
        self.aiguilles = aiguille

    def __str__(self):
        return f"J{self.jetons} A{self.auths} \nE{self.ev} S{self.aiguilles} W{self.waiting}"

    def changeAuth(self, i, auth):
        self.auths[i] = auth
    
    def incrJeton(self, j):
        self.jetons[j] += 1

    def addWait(self, id, pos, valJ):
        self.waiting[(pos, valJ)] = id

    def supprWait(self, pos, valJ):
        if (pos, valJ) in self.waiting:
            id = self.waiting[(pos, valJ)]
            del self.waiting[(pos, valJ)]
            return id
    
    def addEv(self, id, pos, prog):
        nb = self.nbEv[id]
        self.ev[(id, pos, nb)] = prog
        self.nbEv[id] += 1
        
    "numEv chachée du train"
    def getEv(self, id, pos):
        numEv = self.nextEventNum[id]
        if (id, pos, numEv) in self.ev:
            prog = self.ev[(id, pos, numEv)]
            return prog
        
    def getEvByNum(self, id, numEv):
        if numEv < self.nbEv[id]:
            for key in self.ev.keys():
                if key[0] == id and key[2] == numEv:
                    return self.ev[key], key[1]
    
    def supprEv(self, id, pos):
        numEv = self.nextEventNum[id]
        if (id, pos, numEv) in self.ev:
            del self.ev[(id, pos, numEv)]
            self.nextEventNum[id] += 1

class Train:
    def __init__(self, id, pos, prog):
        self.id = id
        self.pos = pos
        self.dir = "*"
        self.prog = prog

    def __str__(self):
        return f"{self.pos}/{self.dir} : {self.prog}"
    
    def __repr__(self):
        return str(self)
    
    def addProg(self, prog):
        self.prog += prog

    def depileProg(self):
        if len(self.prog) > 0:
            del self.prog[0]

    def nextProg(self):
        if len(self.prog) > 0:
            return self.prog[0]
        else:
            return None
        
##### Utilitaires #####

#switch réservé 
""" def switchRes(id_train, id_switch, reg):
    if id_train in reg.aiguilles[id_switch]:
        return True
    return False """

def suivant(pos,dir,reg):
    circuit = reg.circuit
    aiguille = reg.aiguilles
    concat = str(pos) + dir
    if concat in circuit:
        for neigh, switch in circuit[concat].items():
            if switch is None:
                return neigh #, None
            
            nbSwitchOk = 0
            #switchID = []
            for i in range(0, len(switch)):

                num = switch[i][0]
                val = switch[i][1]
                #switchID.append(num)
                if val != aiguille[num]:
                    break
                nbSwitchOk += 1
            if nbSwitchOk == len(switch):
                return neigh #, switchID
    return None #, None

    
def findById(id, gamma):
    if id in gamma:
        return gamma[id]


def nextAtt(T, R):
    id_train = T.id
    cpt = R.nextEventNum[id_train]
    while cpt < R.nbEv[id_train]:
        prog, pos_event = R.getEvByNum(id_train, cpt)
        if prog is None:
            return None
        for instr in prog:
            if instr.startswith("att"):
                return pos_event
        cpt += 1
    #Pas de prochain event contenant "att", c'est qu'on peut aller à l'objectif
    for i in range(len(T.prog)-1,-1,-1):
        if T.prog[i].startswith("Until"):
            return int(T.prog[i][6])
                 

def apply(T, R, gamma):
    id = T.id
    pos = T.pos
    prog = R.getEv(id, pos)
    R.supprEv(id, pos)
    while prog:
        if prog[0].startswith("att"):
            wPos = int(prog[0][4])
            wVal = int(prog[0][6])
            if R.jetons[wPos] != wVal:
                R.auths[id] = pos
                R.addWait(id, wPos, wVal)
            else:
                R.auths[id] = nextAtt(T, R)
        elif prog[0].startswith("incr"):
            jeton = int(prog[0][5])
            R.incrJeton(jeton)
            w_id = R.supprWait(jeton, R.jetons[jeton])
            if w_id is not None:
                T_w = findById(w_id, gamma)
                R.auths[w_id] = nextAtt(T_w, R)
        elif prog[0].startswith("turn"):
            id_switch = int(prog[0][5])
            val_switch = prog[0][7]
            R.aiguilles[id_switch] = val_switch
        else:
            break
        prog.pop(0)

###### Regles ######

def start(T):
    if T.nextProg() is None:
        return None
    if T.dir == "*" and T.nextProg().startswith("Start"):
        T.dir = T.nextProg()[6]
        T.depileProg()
        return True

def stop(T):
    if T.nextProg() is None:
        return None
    if T.nextProg() == "Stop()":
        T.dir = "*"
        T.depileProg()
        return True
    
def until(T, R):
    if T.nextProg() is None:
        return None

    #neigh, switch = suivant(T.pos, T.dir, R)
    neigh = suivant(T.pos, T.dir, R)

    """ resa = True # True si les aiguillage sont réservés pour le train T
    if switch is not None:
        for i in range(0, len(switch)):
            resa = resa and switchRes(T.id, switch[i], R) """
    prog = T.nextProg()
    ev = R.getEv(T.id, neigh)
    if ev is None and neigh is not None: # Pas d'event et un voisin
        if prog.startswith("Until") and neigh != int(prog[6]):
            if T.pos != neigh and R.auths[T.id] != T.pos:
                T.pos = neigh
                return True

def until_cons(T,R):
    if T.nextProg() is None:
        return None

    #neigh, switch = suivant(T.pos, T.dir, R)
    neigh = suivant(T.pos, T.dir, R)

    """ resa = True # True si les aiguillage sont réservés pour le train T
    if switch is not None:
        for i in range(0, len(switch)):
            resa = resa and switchRes(T.id, switch[i], R) """
    
    prog = T.nextProg()
    ev = R.getEv(T.id, neigh)
    if ev is None and neigh is not None: # Pas d'event et un voisin
        if prog.startswith("Until") and neigh == int(prog[6]):
            if T.pos != neigh and R.auths[T.id] != T.pos:
                T.pos = neigh
                T.depileProg()
                return True
        
def until_ev(T,R,gamma):
    if T.nextProg() is None:
        return None

    #neigh, switch = suivant(T.pos, T.dir, R)
    neigh = suivant(T.pos, T.dir, R)

    """ resa = True # True si les aiguillage sont réservés pour le train T
    if switch is not None:
        for i in range(0, len(switch)):
            resa = resa and switchRes(T.id, switch[i], R) """

    prog = T.nextProg()
    ev = R.getEv(T.id, neigh)
    if ev and neigh is not None:
        if prog.startswith("Until") and neigh != int(prog[6]):
            if T.pos != neigh and R.auths[T.id] != T.pos:
                T.pos = neigh
                apply(T, R, gamma)
                return True

def until_cons_ev(T,R,gamma):
    if T.nextProg() is None:
        return None

    #neigh, switch = suivant(T.pos, T.dir, R)
    neigh = suivant(T.pos, T.dir, R)

    """ resa = True # True si les aiguillage sont réservés pour le train T
    if switch is not None:
        for i in range(0, len(switch)):
            resa = resa and switchRes(T.id, switch[i], R) """
    
    prog = T.nextProg()
    ev = R.getEv(T.id, neigh)
    if ev and neigh is not None:
        if prog.startswith("Until") and neigh == int(prog[6]):
            if T.pos != neigh and R.auths[T.id] != T.pos:
                T.pos = neigh
                apply(T, R, gamma)
                T.depileProg()
                return True
            
def wait(T,R, gamma):
    ev = R.getEv(T.id, T.pos)
    if ev and R.auths[T.id] == T.pos:
        if ev[0].startswith("att"):
            apply(T, R, gamma)
            return True

#T et U deux trains
def crash(T, U):
    if T.id != U.id and T.pos == U.pos:
        return True


if __name__ == "__main__":
    circuit = {
        "0R" : {1 : None},
        "1R" : {2 : [(0,"d")], 3 : [(0,"v")]},
        "1L" : {0 : None},
        "2L" : {1 : [(0,"d")]},
        "3L" : {1 : [(0,"v")]},
    }
    #Todo : changer suivant et switchRes
    #Todo : modifier les règles Until

    aig = ["d"]

    reg = Regul(4, [2,3], circuit, aig)
    car = Train(0,0,["Start(R)","Until(2)","Stop()"])
    tri = Train(1,3,["Start(L)","Until(0)","Stop()"])

    Gamma = dict()
    Gamma[0] = car
    Gamma[1] = tri

    reg.addEv(0,2,["incr(1)","turn(0,v)"])
    reg.addEv(1,3,["att(1,1)"])


"""     print("-- Init --")
    print(f"{reg}\n{car}\n{tri}")

    start(car)
    print(f"{reg}\n{car}\n{tri}")

    start(tri)
    print(f"{reg}\n{car}\n{tri}")

    wait(tri, reg, Gamma)
    print(f"{reg}\n{car}\n{tri}")

    until(car, reg)
    print(f"{reg}\n{car}\n{tri}")

    until_cons_ev(car, reg, Gamma)
    print(f"{reg}\n{car}\n{tri}")

    until(tri, reg)
    print(f"{reg}\n{car}\n{tri}")

    until_cons(tri, reg)
    print(f"{reg}\n{car}\n{tri}")

    stop(tri)
    print(f"{reg}\n{car}\n{tri}")

    stop(car)
    print(f"{reg}\n{car}\n{tri}") """
