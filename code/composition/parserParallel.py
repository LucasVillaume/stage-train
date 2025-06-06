import re
import json

def parseGraph(path):
    cpt = 0
    etat = dict()

    with open(path, 'r') as file:
        for line in file:
            if "->" in line and cpt != 180133:
                #extraction
                key = re.findall(r'N\d+[RLO]\d+[RLO]\d+[RLO] -> N\d+[RLO]\d+[RLO]\d+[RLO]', line)[0]
                value = re.findall(r'".*"', line)[0]
                #traitement
                key = key.replace("O", "*")
                value = value.replace('"', '')
                etat[key] = value[2:] #retire les deux premiers __
                print(f"key: {key} value: {value}")
            cpt += 1
    return etat


def simplifyGraph(save=False):
    with open("etat_elem.json", "r") as file:
        etat = json.load(file)

    graph = dict()
    for states, transitions in etat.items():
        e1, e2 = states.split(" -> ")
        if e1 not in graph:
            graph[e1] = dict()
        graph[e1][e2] = transitions

    if save:
        with open("graph_simple.json", "w") as file:
            json.dump(graph, file, indent=4)
    
    return graph
    

if __name__ == "__main__":
    """ etat = parseGraph("parallel_mouvement.dot")

    # enregistre le dictionnaire dans un fichier json
    with open("etat_elem.json", "w") as save:
        json.dump(etat, save, indent=4)

    with open("etat.json", "r") as file:
        etat = json.load(file)
        res = etat["N4*5*2* -> N4L5R2*"]
        print(res)
        print([x for x in res.split('__')]) """
    
    graph = simplifyGraph(True)
    print(f"Nombre d'états : {len(graph)}")
    mean = sum(len(transitions) for transitions in graph.values()) / len(graph)
    print(f"Nombre moyen de transitions par état : {mean:.2f}")