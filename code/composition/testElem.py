from composer import createProgram
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





if __name__ == "__main__":
    etats = dict()
    with open("etat_elem.json", "r") as file:
        etats = json.load(file)
    with open("test/testElem.txt", "w") as file:
        file.write(f"Test des trajets élémentaires\n\n")
    
    t = time.time()
    #try:
    for i in range(1000):
        good = False

        while not good or len(etats) == 0:
            good = True
            selected = random.choice(list(etats.keys()))
            saved_etat = etats[selected] 
            etats.pop(selected)
            pos = re.findall(r"\d+[LR*]", selected)
            for j in range(len(pos)-3):
                if "*" in pos[j] and pos[j] != pos[j+3]:
                    good = good and False

        if not good:
            raise ("Plus de trajet pour tester !")
        d, f = selected.split(" -> ")
        p = saved_etat.split("__")
        o1 = createProgram(d, f, p)
        model = trajet2model(o1)
        with open("model/composition.tla", "w") as file:
            file.write(model)
        with open("test/testElem.txt", "a") as file:
            file.write(f"Trajet {i+1} : {selected}\n") 
        execution()
        afficher_progression(i + 1, 1000)
    """ except Exception as e:
        print(f"{e}")
        print("Fin de la génération des trajets.") """
    print(f"Temps d'exécution : {time.time() - t} secondes")
