from composer import compose, createProgram, build_troncons, Trajet, Train
from TLAModel import trajet2model
from math import ceil
from multiprocessing import Process, Array, Value, Event
from datetime import datetime
import json
import subprocess
import re
import time
import random
import signal
import os
import sys
import pickle


etats = dict()
with open("graph_simple.json", "r") as file:
    etats = json.load(file)

save_etats = dict()
with open("graph_simple.json", "r") as file:
    save_etats = json.load(file)

def handler(signum, frame):
    global term_event
    term_event.set()
    print("Arrêt propre du programme.")

def ignore_sigint():
    signal.signal(signal.SIGINT, signal.SIG_IGN)


def setup(e1, e2, e3, dir="model"):
    p1 = save_etats[e1][e2].split("__")
    p2 = save_etats[e2][e3].split("__")

    o1 = createProgram(e1, e2, p1)
    o2 = createProgram(e2, e3, p2)
    o3 = compose(o1, o2, True)

    model = trajet2model(o3, build_troncons(o3.trains))
    with open(f"{dir}/composition.tla", "w") as file:
        file.write(model)

def setupComplex(comp, e2, e3, dir="model"):
    p2 = save_etats[e2][e3].split("__")
    o2 = createProgram(e2, e3, p2)
    o3 = compose(comp, o2)

    model = trajet2model(o3, build_troncons(o3.trains))
    with open(f"{dir}/composition.tla", "w") as file:
        file.write(model)

def check(etat1, etat2, etat3):
    pos = []
    pos.append(re.findall(r"\d+[LR*]", etat1))
    pos.append(re.findall(r"\d+[LR*]", etat2))
    pos.append(re.findall(r"\d+[LR*]", etat3))

    for i in range(len(pos[0])):
        if pos[0][i] != pos[1][i] and pos[0][i] == pos[2][i]:
            #non conforme pour l'analyse TLA
            #A -> B -> C : A != B mais A == C
            #ça implique X(RL) -> X* -> X(RL) ou X* -> X(RL) -> X*
            return False

    for i in range(len(pos[1])):
        if "*" in pos[1][i] and pos[1][i] != pos[2][i]:
            #non conforme pour l'analyse TLA
            return False
    return True

def checkComplexe(etat1, etat2, etat3):
    pos = []
    pos.append(re.findall(r"\d+[LR*]", etat1))
    pos.append(re.findall(r"\d+[LR*]", etat2))
    pos.append(re.findall(r"\d+[LR*]", etat3))

    for i in range(len(pos[0])):
        if "*" in pos[2][i] and pos[1][i] != pos[2][i]:
            #non conforme pour l'analyse TLA
            return False

    for i in range(len(pos[1])):
        if "*" in pos[1][i] and pos[1][i] != pos[2][i]:
            #non conforme pour l'analyse TLA
            return False
    return True

def execution(dir="model"):
    command = ["java", "-jar", f"model/tla2tools.jar", "-noGenerateSpecTE", "-workers", "2","-config", f"model/compo.cfg", f"{dir}/model2.tla"]
    if dir != "model":
        command.insert(4,"-metadir")
        command.insert(5, dir+"/tmp")

    f = open(f"{dir}/out.log", "w")
    p = subprocess.Popen(command, stdout=f, stderr=f, preexec_fn=ignore_sigint)
    p.wait()
    f.close()

    if p.returncode != 0:
        raise Exception(f"Erreur lors de l'exécution du modèle TLA+. Veuillez vérifier {dir}/out.log pour plus de détails.")
    else:
        with open(f"{dir}/out.log", "r") as output:
            warn = re.findall(r"Warning:.*", "".join(output.readlines()))
            if len(warn) > 1:
                raise Exception(f"Warnings trouvés dans le fichier de log. Veuillez vérifier {dir}/out.log pour plus de détails.")



def analyse(data=None, dir=None, term_event=None, tab=None):

    if data is None:
        data = etats

    cpt = 0
    total_erreurs = 0

    while len(data) > 0 and not term_event.is_set():
        etat1 = random.choice(list(data.keys()))
        for pkl in data[etat1]:
            with open(f"model/pickle/{pkl}", "rb") as file:
                tmp = file.read()
                complex = pickle.loads(tmp)
            for etat3 in save_etats[etat1].keys():
                try:
                    if checkComplexe(complex.posInitial, etat1, etat3):
                        t = time.time()
                        if dir is None:
                            setupComplex(complex, etat1, etat3)
                            execution()
                        else:
                            setupComplex(complex, etat1, etat3, dir)
                            execution(dir)
                        cpt += 1
                        """ if tab is None:
                            print(f"Execution {cpt} : {etat1} -> {etat2} -> {etat3} en {time.time() - t:.2f} secondes")
                        else:
                            tab[1] += 1"""
                        with open(f"{dir}/succes.log", "a") as file:
                            file.write(f"{complex.posInitial} -> {etat1} -> {etat3} en {time.time() - t:.2f} secondes\n")
                except Exception as e:
                    total_erreurs += 1
                    """ if tab is None:
                        print(f"Erreur {etat1} -> {etat2} -> {etat3}: {e} / Nombre total d'erreurs: {total_erreurs}")
                    else:
                        tab[0] += 1
                        print(f"Erreur entre {etat1}, {etat2} et {etat3}: {e} / Nombre total d'erreurs: {tab[1]}") """
                    with open(f"{dir}/errors.log","a") as error_file:
                        error_file.write(f"Erreur {complex.posInitial} -> {etat1} -> {etat3} : {e}\n")

        with open(f"{dir}/progress.log", "a") as progress_file:
            progress_file.write(etat1 + "\n")
        data.pop(etat1)

    #print(f"Travail terminé. Sauvegarde en cours...")
    save_path = "model/save_etats.json"
    if dir is not None:
        save_path = f"{dir}/save_etats.json"

    with open(save_path,"w") as save_file:
        json.dump(data, save_file, indent=4)


def affichage(array, term):
    while term != True:
        total = [0,0]
        for i in range(len(array)):
            total[0] += array[i][0]
            total[1] += array[i][1]
        print(f"Total erreurs : {total[0]} / Total executions : {total[1]}")
        time.sleep(2)


def manager(pid):
    """ Contrôle la durée de l'expérience """
    for i in range(10):
        time.sleep(3600) # Laisser le temps aux processus de s'exécuter
    os.kill(pid, signal.SIGINT)


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



if __name__ == "__main__":

    nodeData = etats    

    if len(sys.argv) > 1:
        with open(f"model/gp_{sys.argv[1]}.json","r") as file:
            nodeData = json.load(file)


    print(f"Début de l'analyse : {datetime.now().strftime('%d-%m-%Y %H:%M:%S')}")

    signal.signal(signal.SIGINT, signal.SIG_IGN)
    term_event = Event()

    divided = divide_dict(nodeData, 5)


    d_procs = divided
    procs = []
    #arrays = []
    for i in range(len(d_procs)):
        #arrays.append(Array('i', [0, 0]))
        #p = Process(target=analyse, args=(d_procs[i], "model/compo"+str(i+1), arrays[i], term_event))
        p = Process(target=analyse, args=(d_procs[i], "model/node"+sys.argv[1]+"/compo"+str(i+1), term_event,))
        procs.append(p)
        p.start()

    #p_aff = Process(target=affichage, args=(arrays, False)) #utiliser Value pour le paramètre term
    #p_aff.start()

    p_manager = Process(target=manager, args=(os.getpid(),))
    p_manager.start()

    signal.signal(signal.SIGINT, handler)

    for p in procs:
        p.join()
    
    if p_manager.is_alive():
        p_manager.kill()

    print(f"Fin de l'analyse : {datetime.now().strftime('%d-%m-%Y %H:%M:%S')}")

    #p_aff.kill()

    """ term_event = Event()
    signal.signal(signal.SIGINT, handler)
    analyse(term_event=term_event) """


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

