from composer import createProgram
from composer import clean_turns
from composer import addAuth
from TLAModel import trajet2model
from main import execution
import json
import random
import time
import re
import sys



r = 108
g = 66
b = 158
RESET = "\033[0m"
color = f"\033[38;2;{r};{g};{b}m"

def afficher_progression(current, total, largeur=40):
    progress = int(largeur * current / total)
    bar = '█' * progress + '-' * (largeur - progress)
    sys.stdout.write(f"\r{color}[{bar}]{RESET} {current}/{total}")
    sys.stdout.flush()


def preparation(o1):
    clean_turns(o1)
    addAuth(o1)
    

if __name__ == "__main__":

    version = ""
    if len(sys.argv) > 1:
        version = sys.argv[1]

    etats = dict()
    with open("etat_elem.json", "r") as file:
        etats = json.load(file)

    total = len(etats)
    t = time.time()
    i = 0

    while len(etats) > 0:
    #for i in range(total):
        good = False


        try:
            #recherche un trajet à tester
            while not good or len(etats) == 0:
                good = True
                selected = random.choice(list(etats.keys()))
                saved_etat = etats[selected] 
                etats.pop(selected)
                pos = re.findall(r"\d+[LR*]", selected)
                for j in range(len(pos)-3):
                    if "*" in pos[j] and pos[j] != pos[j+3]: #traite pas les trains qui démarrent juste
                        good = good and False

            if not good:
                raise ("Plus assez de trajet pour tester !")
            
            d, f = selected.split(" -> ")
            p = saved_etat.split("__")
            o1 = createProgram(d, f, p)

            preparation(o1)
            model = trajet2model(o1)
            with open("model/composition.tla", "w") as file:
                file.write(model)

            execution()
            
            with open("test/testElem"+version+".txt", "a") as file:
                file.write(f"Trajet {i+1} : {selected}\n")
        except Exception as e:
            with open("test/errorElem"+version+".log", "a") as file:
                file.write(f"Trajet {i+1} : {selected} | {e}\n")
        finally:
            i += 1
            afficher_progression(i + 1, total)

    print(f"\nTemps d'exécution : {time.time() - t} secondes")
