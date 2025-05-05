import re


def circuit2fct(circuit):
    fct = ""
    first = True
    for key, value in circuit.items():
        # posDir[0] = position, posDir[1] = direction
        posDir = re.findall(r"[0-9]+|[LR]", key)
        for target, aig in value.items():
            if first:
                fct += 'IF '
                first = False
            else:
                fct += 'ELSE IF '
            fct += f'pos = "{int(posDir[0])+1}" /\\ dir = "{posDir[1]}" '
            if aig != None:
                for i in range(len(aig)):
                    fct += f'/\\ S[{aig[i][0]+1}] = "{aig[i][1]}" '
            fct += f'THEN "{target+1}"\n'
    fct += 'ELSE "-1"\n'
    return fct

            
        
