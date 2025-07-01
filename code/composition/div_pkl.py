from main_parallele import divide_dict
import json
import sys

etats = dict()
with open("pickle.json", "r") as file:
    etats = json.load(file)

nb = 1
if len(sys.argv) > 1:
    nb = int(sys.argv[1])
    if nb < 1:
        raise ValueError("Number of divisions must be at least 1.")


div = divide_dict(etats, nb)

s = 0
for d in div:
    s += len(d)

if s != len(etats):
    print(f"Error: Total items {s} does not match original {len(etats)}")
    raise ValueError("Mismatch in total items after division.")
else:
    print(f"Total items: {s}")

#check si pas de doublons entre les dictionnaires
for d1 in div:
    for d2 in div:
        if d1 is d2:
            continue
        intersection = set(d1.keys()).intersection(set(d2.keys()))
        if intersection:
            print(f"Error: Duplicates found between dictionaries: {intersection}")
            raise ValueError("Duplicates found in divided dictionaries.")
        



i = 0
for d in div:
    with open(f"model/gp_{i}.json", "w") as file:
        json.dump(d, file, indent=4)
    i += 1

