from composer import compose
from composer import createProgram
from TLAModel import trajet2model
from math import ceil
from multiprocessing import Process, Array, Value
import json
import subprocess
import re
import time

g_etats = dict()
with open("etat_elem.json", "r") as file:
    g_etats = json.load(file)


def setup(d1, f1, d2, f2, dir="model"):
    etats = g_etats

    e1 = etats[d1 + " -> " + f1].split("__")
    e2 = etats[d2 + " -> " + f2].split("__")

    o1 = createProgram(d1, f1, e1)
    o2 = createProgram(d2, f2, e2)
    o3 = compose(o1, o2)

    model = trajet2model(o3)
    with open(f"{dir}/composition.tla", "w") as file:
        file.write(model)
    

def execution(dir="model"):
    comand = ["java", "-jar", f"model/tla2tools.jar", "-noGenerateSpecTE", "-config", f"model/compo.cfg", f"{dir}/model1.tla"]
    if dir != "model":
        comand.insert(4,"-metadir")
        comand.insert(5, dir+"/tmp")

    f = open(f"{dir}/out.log", "w")
    res = subprocess.call(comand, stdout=f, stderr=f)
    f.close()

    if res != 0:
        raise Exception(f"Erreur lors de l'exécution du modèle TLA+. Veuillez vérifier {dir}/out.log pour plus de détails.")
    else:
        with open(f"{dir}/out.log", "r") as output:
            warn = re.findall(r"Warning:.*", "".join(output.readlines()))
            if len(warn) > 1:
                raise Exception(f"Warnings trouvés dans le fichier de log. Veuillez vérifier {dir}/out.log pour plus de détails.")


def check(etat1, etat2):
    pos = []
    pos.append(re.findall(r"\d+[LR*]", etat1))
    pos.append(re.findall(r"\d+[LR*]", etat2))

    for i in range(len(pos[0])-3):
        if pos[0][i] != pos[0][i+3] and pos[0][i] == pos[1][i+3]:
            #non conforme pour l'analyse TLA
            #A -> B -> C : A != B mais A == C
            #ça implique X(RL) -> X* -> X(RL) ou X* -> X(RL) -> X*
            return False    

    for i in range(len(pos[1])-3):
        if "*" in pos[1][i] and pos[1][i] != pos[1][i+3]:
            #non conforme pour l'analyse TLA
            return False
    return True


def divide_dict(d,n):
    q = len(d) / n
    dicts = []
    items = list(d.items())

    for i in range(n):
        if i != n-1:
            dicts.append(items[ceil(i*q):ceil((i+1)*q)])
        else: #n-1
            dicts.append(items[ceil(i*q):])
    return [dict(i) for i in dicts]


def analyse(data=None, dir=None, tab=None):
    etats = g_etats
    if data is None:
        data = etats

    cpt = 0
    total_erreurs = 0

    for etat1 in data.keys():
        for etat2 in etats.keys():
            try:
                if check(etat1, etat2):
                    t = time.time()
                    s1, e1 = etat1.split(" -> ")
                    s2, e2 = etat2.split(" -> ")
                    if etat1 != etat2 and e1 == s2:
                        if dir is None:
                            setup(s1, e1, s2, e2)
                            execution()
                        else:
                            setup(s1, e1, s2, e2, dir)
                            execution(dir)
                        cpt += 1
                        if tab is None:
                            print(f"Execution {cpt} : {etat1} et {etat2} en {time.time() - t:.2f} secondes")
                        else:
                            tab[1] += 1
            except Exception as e:
                total_erreurs += 1
                if tab is None:
                    print(f"Erreur entre {etat1} et {etat2}: {e} / Nombre total d'erreurs: {total_erreurs}")
                else:
                    tab[0] += 1
                    print(f"Erreur entre {etat1} et {etat2}: {e} / Nombre total d'erreurs: {tab[1]}")
                with open("model/errors.log","a") as error_file:
                    error_file.write(f"Erreur entre {etat1} et {etat2} : {e}\n")
                #exit(1)


def affichage(array, term):
    while term != True:
        total = [0,0]
        for i in range(len(array)):
            total[0] += array[i][0]
            total[1] += array[i][1]
        print(f"Total erreurs : {total[0]} / Total executions : {total[1]}")
        time.sleep(2)

if __name__ == "__main__":
    etats = g_etats

    """ divided = divide_dict(etats, 100)

    d_procs = [divided[1],divided[2]]
    procs = []
    arrays = []
    for i in range(len(d_procs)):
        arrays.append(Array('i', [0, 0]))
        p = Process(target=analyse, args=(d_procs[i], "model/compo"+str(i+1), arrays[i]))
        procs.append(p)
        p.start()

    p_aff = Process(target=affichage, args=(arrays, False)) #utiliser Value pour le paramètre term
    p_aff.start() """
    

    analyse()


    """ t = time.time()
    etat1 = "N4R1*5* -> N2R1*5L"
    etat2 = "N2R1*5L -> N2*1*6L"
    s1, e1 = etat1.split(" -> ")
    s2, e2 = etat2.split(" -> ")

    if check(etat1, etat2):
        print(f"Setting up for {etat1} and {etat2}")
        setup(s1, e1, s2, e2)
        execution()
        print(f"Execution time: {time.time() - t:.2f} seconds") """

