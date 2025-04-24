import re

class Regul:
    def __init__(self, nbJ, auths, circuit, aiguille):
        self.jetons = [0]*nbJ
        self.auths = auths # tableau de compteur qui décrémente
        self.ev = dict() # couple (idTrain, numEvent) -> prog
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
        return self.jetons[j]
    
    def getValJeton(self, j):
        return self.jetons[j]

    def addWait(self, id, pos, valJ):
        self.waiting[(pos, valJ)] = id

    def supprWait(self, pos, valJ):
        if (pos, valJ) in self.waiting:
            id = self.waiting[(pos, valJ)]
            del self.waiting[(pos, valJ)]
            return id
    
    def addEv(self, id, numEv, prog):
        self.ev[(id, numEv)] = prog
        self.nbEv[id] += 1
        
    # Retourne l'event courant pour le train id
    def getEv(self, id):
        numEv = self.nextEventNum[id]
        return self.getEvByNum(id, numEv)
        
    def getEvByNum(self, id, numEv):
        if (id, numEv) in self.ev:
            prog = self.ev[(id, numEv)]
            return prog
    
    # Supprime l'event courant pour le train id
    def supprEv(self, id):
        numEv = self.nextEventNum[id]
        self.supprEvByNum(id, numEv)

    def supprEvByNum(self, id, numEv):
        if (id, numEv) in self.ev:
            del self.ev[(id, numEv)]

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

#Retourne le prochian tronçon 
def suivant(pos,dir,reg):
    circuit = reg.circuit
    aiguille = reg.aiguilles
    concat = str(pos) + dir
    
    #cherche si la position actuelle possède un voisin
    if concat in circuit:
        for neigh, switch in circuit[concat].items():
            if switch is None:
                return neigh
            
            nbSwitchOk = 0
            #On vérifie si les aiguillages sont dans le bon état
            for i in range(0, len(switch)):

                num = switch[i][0]
                val = switch[i][1]
                if val != aiguille[num]:
                    break
                nbSwitchOk += 1
            if nbSwitchOk == len(switch):
                return neigh
    return None

#Cherche un train dans la gamma via son id
def findById(id, gamma):
    if id in gamma:
        return gamma[id]

#Retourne la position du prochian event contenant "att"
#ou la distance au dernier event si il n'y en a pas
def nextAtt(T, R):
    id_train = T.id
    cpt = R.nextEventNum[id_train]
    auth = 0
    #cherche dans les prochains events
    while cpt < R.nbEv[id_train]:
        prog = R.getEvByNum(id_train, cpt)
        if prog is not None:
            for instr in prog:
                if instr.startswith("att"):
                    return auth
        cpt += 1
        auth +=1
    #retourne la distance au dernier event
    return auth 




###### Regles ######

def start(T):
    if T.nextProg() is None:
        return None
    
    prog = T.nextProg()
    dirStart = re.findall(r"[LR*]", prog)[0]

    if T.dir != dirStart and prog.startswith("StartUntil"):
        T.dir = dirStart
        return True

def stop(T,R):
    ev = R.getEv(T.id)
    if T.nextProg() is None and T.dir != "*" and ev is None:
        T.dir = "*"
        return True
        
def until(T,R):
    ev = R.getEv(T.id)
    if T.nextProg() is None or ev is not None:
        return None

    neigh = suivant(T.pos, T.dir, R)
    prog = T.nextProg()
    #args : [dir, pos] de StartUntil(dir, pos)
    args = re.findall(r"[0-9]+|[LR*]", prog)

    if neigh is not None:
        if prog.startswith("StartUntil") and neigh != int(args[1]):
            if T.pos != neigh and R.auths[T.id] != 0 and T.dir == args[0]:
                T.pos = neigh
                R.nextEventNum[T.id] += 1
                R.auths[T.id] -= 1
                return True

def until_cons(T,R):
    ev = R.getEv(T.id)
    if T.nextProg() is None or ev is not None:
        return None

    neigh = suivant(T.pos, T.dir, R)    
    prog = T.nextProg()
    #args : [dir, pos] de StartUntil(dir, pos)
    args = re.findall(r"[0-9]+|[LR*]", prog)

    if neigh is not None:
        if prog.startswith("StartUntil") and neigh == int(args[1]):
            if T.pos != neigh and R.auths[T.id] != 0 and T.dir == args[0]:
                T.pos = neigh
                T.depileProg()
                R.nextEventNum[T.id] += 1
                R.auths[T.id] -= 1
                return True
            

def elimEv(T,R):
    ev = R.getEv(T.id)
    if ev is not None and ev == []:
        R.supprEv(T.id)
        return True


def incr_bf(T,R):
    ev = R.getEv(T.id)
    if ev and ev[0].startswith("incr"):
        token = re.findall(r"[0-9]+", ev[0])[0]
        value_t = R.getValJeton(int(token))
        if (int(token), value_t+1) not in R.waiting: #incr avant att
            R.incrJeton(int(token))
            ev.pop(0) #dépile l'event
            return True


def incr_af(T,R,gamma):
    ev = R.getEv(T.id)
    if ev and ev[0].startswith("incr"):
        token = re.findall(r"[0-9]+", ev[0])[0]
        value_t = R.getValJeton(int(token))
        if (int(token), value_t+1) in R.waiting: #incr après att
            R.incrJeton(int(token))
            w_id = R.supprWait(int(token), value_t+1)
            R.auths[w_id] = nextAtt(findById(w_id, gamma), R)
            ev.pop(0)
            return True


def att_bf(T,R):
    ev = R.getEv(T.id)
    if ev and ev[0].startswith("att"):
        token, value_t = re.findall(r"[0-9]+", ev[0])
        if R.getValJeton(int(token)) != int(value_t):
            R.addWait(T.id, int(token), int(value_t))
            ev.pop(0) #dépile l'event
            return True


def att_af(T,R):
    ev = R.getEv(T.id)
    if ev and ev[0].startswith("att"):
        token, value_t = re.findall(r"[0-9]+", ev[0])
        if R.getValJeton(int(token)) == int(value_t):
            ev.pop(0)
            R.auths[T.id] = nextAtt(T, R)
            return True
        

def turn(T,R):
    ev = R.getEv(T.id)
    if ev and ev[0].startswith("turn"):
        switch, state = re.findall(r"[0-9]+|[dv]", ev[0])
        R.aiguilles[int(switch)] = state
        ev.pop(0)
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

    reg = Regul(4, [2,0], circuit, aig)
    car = Train(0,0,["StartUntil(R,2)"])
    tri = Train(1,3,["StartUntil(L,0)"])

    Gamma = dict()
    Gamma[0] = car
    Gamma[1] = tri

    reg.addEv(0,2,["incr(1)","turn(0,v)"])
    reg.addEv(1,0,["att(1,1)"])
    reg.addEv(1,2,[])

    print("Avant :")
    print(f"{reg}\nTrain 0 :{car}\nTrain 1 : {tri}\n")

    start(car)
    print(f"start(car)\n{reg}\nTrain 0 :{car}\nTrain 1 : {tri}\n")
    
    start(tri)
    print(f"start(tri)\n{reg}\nTrain 0 :{car}\nTrain 1 : {tri}\n")
    
    until(car, reg)
    print(f"until(car)\n{reg}\nTrain 0 :{car}\nTrain 1 : {tri}\n")
    
    att_bf(tri, reg)
    print(f"att_bf(tri)\n{reg}\nTrain 0 :{car}\nTrain 1 : {tri}\n")

    elimEv(tri, reg)
    print(f"elimEv(tri)\n{reg}\nTrain 0 :{car}\nTrain 1 : {tri}\n")

    until_cons(car, reg)
    print(f"until_cons(car)\n{reg}\nTrain 0 :{car}\nTrain 1 : {tri}\n")

    incr_af(car, reg, Gamma)
    print(f"incr_af(car)\n{reg}\nTrain 0 :{car}\nTrain 1 : {tri}\n")

    turn(car, reg)
    print(f"turn(car)\n{reg}\nTrain 0 :{car}\nTrain 1 : {tri}\n")

    elimEv(car, reg)

    until(tri, reg)
    print(f"until(tri)\n{reg}\nTrain 0 :{car}\nTrain 1 : {tri}\n")

    until_cons(tri, reg)
    print(f"until_cons(tri)\n{reg}\nTrain 0 :{car}\nTrain 1 : {tri}\n")

    elimEv(tri, reg)
    print(f"elimEv(tri)\n{reg}\nTrain 0 :{car}\nTrain 1 : {tri}\n")

    stop(car, reg)
    print(f"stop(car)\n{reg}\nTrain 0 :{car}\nTrain 1 : {tri}\n")

    stop(tri, reg)
    print(f"stop(tri)\n{reg}\nTrain 0 :{car}\nTrain 1 : {tri}\n")


