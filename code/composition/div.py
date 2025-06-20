from main_parallele import divide_dict
import json
import sys

etats = dict()
with open("graph_simple.json", "r") as file:
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

i = 0
for d in div:
    with open(f"model/gs_{i}.json", "w") as file:
        json.dump(d, file, indent=4)
    i += 1

