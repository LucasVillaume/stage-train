#Fichier où on va tester différents scénarios
import algo
import pathfinder


#Modélisation de la maquette
maquette = dict()
maquette['1L'] = {'1*': 1, '3L': 1}
maquette['1*'] = {'1L': 1}
maquette['1R'] = {'1*': 1}

maquette['2L'] = {'2*': 1, '3L': 1}
maquette['2*'] = {'2L': 1}
maquette['2R'] = {'2*': 1}

maquette['3L'] = {'3*': 1, '7L': 1, '8L': 1}
maquette['3*'] = {'3L': 1, '3R': 1}
maquette['3R'] = {'3*': 1, '4R': 1, '1R': 1, '2R': 1}

maquette['4L'] = {'4*': 1, '3L': 1}
maquette['4*'] = {'4L': 1, '4R': 1}
maquette['4R'] = {'4*': 1, '5R': 1, '6R': 1}

maquette['5L'] = {'5*': 1, '4L': 1}
maquette['5*'] = {'5L': 1, '5R': 1}
maquette['5R'] = {'5*': 1, '7R': 1}

maquette['6L'] = {'6*': 1, '4L': 1}
maquette['6*'] = {'6L': 1, '6R': 1}
maquette['6R'] = {'6*': 1, '7R': 1}

maquette['7L'] = {'7*': 1, '5L': 1, '6L': 1}
maquette['7*'] = {'7L': 1, '7R': 1}
maquette['7R'] = {'7*': 1, '3R': 1}

maquette['8L'] = {'8*': 1}
maquette['8*'] = {'8R': 1}
maquette['8R'] = {'8*': 1, '3R': 1}


#Modélisation d'un circuit

simple_1 = dict()
simple_1['1*'] = {'1R': 1}
simple_1['1R'] = {'1*': 1, '2R': 1}
simple_1['1L'] = {'1*': 1}

simple_1['2*'] = {'2R': 1, '2L': 1}
simple_1['2R'] = {'2*': 1, '3R': 1, "10R": 1}
simple_1['2L'] = {'2*': 1, '1L': 1}

simple_1['3*'] = {'3R': 1, '3L': 1}
simple_1['3R'] = {'3*': 1, '4R': 1}
simple_1['3L'] = {'3*': 1, '2L': 1}

simple_1['4*'] = {'4R': 1, '4L': 1}
simple_1['4R'] = {'4*': 1, '5R': 1}
simple_1['4L'] = {'4*': 1, '3L': 1}

simple_1['5*'] = {'5R': 1, '5L': 1}
simple_1['5R'] = {'5*': 1, '6R': 1}
simple_1['5L'] = {'5*': 1, '4L': 1}

simple_1['6*'] = {'6R': 1, '6L': 1}
simple_1['6R'] = {'6*': 1, '7R': 1}
simple_1['6L'] = {'6*': 1, '5L': 1, '8L': 1}

simple_1['7*'] = {'7L': 1}
simple_1['7R'] = {'7*': 1}
simple_1['7L'] = {'7*': 1, '6L': 1}

simple_1['8*'] = {'8R': 1, '8L': 1}
simple_1['8R'] = {'8*': 1, '6R': 1}
simple_1['8L'] = {'8*': 1, '9L': 1}

simple_1['9*'] = {'9R': 1, '9L': 1}
simple_1['9R'] = {'9*': 1, '8R': 1}
simple_1['9L'] = {'9*': 1, '10L': 1}

simple_1['10*'] = {'10R': 1, '10L': 1}
simple_1['10R'] = {'10*': 1, '9R': 1}
simple_1['10L'] = {'10*': 1, '2L': 1}


def scenar1():
    graph = maquette
    checkpoint = [("4*", "5*"), ("8*", "7R"), ("8R", "4*"), ("7*", "4L"), ("7*", "3*")]
    apply(graph, checkpoint)

"""     solution = pathfinder.resolution(graph, checkpoint)
    cheminA = []
    cheminB = []
    for s in solution:
        print(s)
        cheminA.append(s[0])
        cheminB.append(s[1])

    algoA = algo.algoTrain(cheminA)
    algoB = algo.algoTrain(cheminB)
    print("\nAlgo A :")
    for a in algoA:
        print(a)
    print("\nAlgo B :")
    for b in algoB:
        print(b)

    regu = algo.algoRegu(cheminA, cheminB)
    print("\nAlgo regulateur :")
    for r in regu: 
        print(r) """


def scenar2():
    graph = simple_1
    checkpoint = [("1*", "7*"), ("5R", "10L"), ("7*", "1*")]
    apply(graph, checkpoint)



def scenar3():
    graph = maquette
    checkpoint = [("5*", "6*"), ("8R", "7R"), ("8R", "2*"), ("3*", "2*")]
    apply(graph, checkpoint)


def apply(graph, checkpoint):
    solution = pathfinder.resolution(graph, checkpoint)
    cheminA = []
    cheminB = []
    for s in solution:
        print(s)
        cheminA.append(s[0])
        cheminB.append(s[1])

    algoA = algo.algoTrain(cheminA)
    algoB = algo.algoTrain(cheminB)
    print("\nAlgo A :")
    for a in algoA:
        print(a)
    print("\nAlgo B :")
    for b in algoB:
        print(b)

    regu = algo.algoRegu(cheminA, cheminB)
    print("\nAlgo regulateur :")
    for r in regu: 
        print(r)



if __name__ == "__main__":
    scenar1()
