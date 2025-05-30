from composer import compose
from composer import createProgram
from TLAModel import trajet2model
import json
import subprocess
import re
import time

g_etats = dict()
with open("etat_elem.json", "r") as file:
    g_etats = json.load(file)


def setup(d1, f1, d2, f2):
    etats = g_etats

    e1 = etats[d1 + " -> " + f1].split("__")
    e2 = etats[d2 + " -> " + f2].split("__")

    o1 = createProgram(d1, f1, e1)
    o2 = createProgram(d2, f2, e2)
    o3 = compose(o1, o2)

    model = trajet2model(o3)
    with open("model/composition.tla", "w") as file:
        file.write(model)
    

def execution():
    f = open("model/out.log", "w")
    res = subprocess.call(["java", "-jar", "model/tla2tools.jar", "-config", "model/compo.cfg", "model/model1.tla"], stdout=f, stderr=f)
    f.close()

    if res != 0:
        raise Exception("Erreur lors de l'exécution du modèle TLA+.\nVeuillez vérifier model/out.log pour plus de détails.")
    else:
        with open("model/out.log", "r") as output:
            warn = re.findall(r"Warning:.*", "".join(output.readlines()))
            if len(warn) > 1:
                print("Warnings:")
                for w in range(1,len(warn)):
                    print("    "+warn[w])
                raise Exception("Warnings trouvés dans le fichier de log. Veuillez vérifier model/out.log pour plus de détails.")


def check(etat1, etat2):
    pos = []
    pos.append(re.findall(r"\d+[LR*]", etat1))
    pos.append(re.findall(r"\d+[LR*]", etat2))

    for i in range(len(pos[0])-3):
        if pos[0][i] != pos[0][i+3] and pos[0][i] == pos[1][i+3]:
            #non conforme pour l'analyse TLA
            return False    

    for i in range(len(pos[1])-3):
        if "*" in pos[1][i] and pos[1][i] != pos[1][i+3]:
            #non conforme pour l'analyse TLA
            return False
    return True


if __name__ == "__main__":
    etats = g_etats
    cpt = 0
    
    e1 = ""
    e2 = ""

    for etat1 in etats.keys():
        for etat2 in etats.keys():
            try:
                if check(etat1, etat2):
                    t = time.time()
                    s1, e1 = etat1.split(" -> ")
                    s2, e2 = etat2.split(" -> ")
                    if etat1 != etat2 and e1 == s2:
                        setup(s1, e1, s2, e2)
                        execution()
                        cpt += 1
                        print(f"Execution {cpt} : {etat1} et {etat2} en {time.time() - t:.2f} secondes")
            except Exception as e:
                print(f"Erreur entre {etat1} et {etat2}: {e}")
                exit(1)

    """ t = time.time()
    etat1 = "N4L5R2* -> N8L7R2*"
    etat2 = "N8L7R2* -> N8*4R2*"
    s1, e1 = etat1.split(" -> ")
    s2, e2 = etat2.split(" -> ")

    if check(etat1, etat2):
        print(f"Setting up for {etat1} and {etat2}")
        setup(s1, e1, s2, e2)
        execution()
        print(f"Execution time: {time.time() - t:.2f} seconds") """