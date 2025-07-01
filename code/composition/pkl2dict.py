import json
import os

dict = {}
files = os.listdir('model/pickle')
for file in files:
    spl = file.split('-')
    if spl[1][:-4].replace('o', '*') not in dict:
        dict[spl[1][:-4].replace('o', '*')] = [file]
    else:
        dict[spl[1][:-4].replace('o', '*')].append(file)


with open('pickle.json', 'w') as f:
    json.dump(dict, f, indent=4)