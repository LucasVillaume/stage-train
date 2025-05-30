

""" Création de l'algorithme du train à partir d'un chemin """
def algoTrain(chemin):

    instr = []
    stop = True
    for step in chemin:
        if stop and step[-1] != '*':
            instr.append(f'Start({step[-1]})')
            stop = False
        if not stop and step[-1] == '*':
            instr.append(f'Until({step[:-1]})')
            instr.append('Stop()')
            stop = True
    
    return instr



class Event:
    def __init__(self, name):
        self.name = name
        self.instructions = []

    def __str__(self):
        s = f"event({self.name})"
        for i in self.instructions:
            s += f"\n\t{i}"
        return s

    def __repr__(self):
        return self.__str__()



""" Création de l'algorithme du régulateur à partir des chemins """
def algoRegu(cheminA, cheminB):
    events = dict()
    critical_index = 0

    token = [0]*10

    ressA = []
    ressB = []

    for i in range(len(cheminA)):
        if cheminA[i-1][:-1] != cheminA[i][:-1]:
            ressA.append(cheminA[i][:-1])
        if cheminB[i-1][:-1] != cheminB[i][:-1]:
            ressB.append(cheminB[i][:-1])


    #Ressource A toujours plus grand
    if len(ressA) < len(ressB):
        tmp = ressA
        ressA = ressB
        ressB = tmp


    for i in range(len(ressA)):
            limit = i if i < len(ressB) else len(ressB)
            for j in range(critical_index, limit):
                if ressA[i] == ressB[j]:
                    critical_index = j if j < i else i
                    ress_crit = int(ressA[i])
                    ev = "A,"+ressA[i-1]
                    if ev not in events:
                        events[ev] = Event(ev)
                    token[ress_crit] += 1
                    events[ev].instructions.append(f"attendre({ress_crit},{token[ress_crit]})")
                    
                    ress_crit = int(ressB[j])
                    ev = "B,"+ressB[j+1]
                    if ev not in events:
                        events[ev] = Event(ev)
                    events[ev].instructions.append(f"ecrire({ress_crit},{token[ress_crit]})")

                if ressA[j] == ressB[i]:
                    critical_index = j if j < i else i
                    ress_crit = int(ressB[i])
                    ev = "B,"+ressB[i-1]
                    if ev not in events:
                        events[ev] = Event(ev)
                    token[ress_crit] += 1
                    events[ev].instructions.append(f"attendre({ress_crit},{token[ress_crit]})")
                    
                    ress_crit = int(ressA[j])
                    if j == len(ressA)-1:
                        ress_crit = int(ressA[j])
                    else:
                        ev = "A,"+ressA[j+1]
                    if ev not in events:
                        events[ev] = Event(ev)
                    events[ev].instructions.append(f"ecrire({ress_crit},{token[ress_crit]})")
    return list(events.values())