from copy import deepcopy
import heapq



""" PLus court chemin """
def djikstra(graph,start,end):
    res = deepcopy(graph)
    
    for node in res:
        res[node] = {'dist' : float('inf'), 'prev' : None}
    res[start]['dist'] = 0
    visited = set()
    while len(visited) != len(graph):
        min_node = None
        for node in res:
            if node not in visited:
                if min_node is None:
                    min_node = node
                elif res[node]['dist'] < res[min_node]['dist']:
                    min_node = node
        for neighbour, weight in graph[min_node].items():
            if neighbour not in visited:
                new_dist = res[min_node]['dist'] + weight
                if new_dist < res[neighbour]['dist']:
                    res[neighbour]['dist'] = new_dist
                    res[neighbour]['prev'] = min_node
        visited.add(min_node)
    #print(res)
    path = []
    current = end
    while current is not None:
        path.append(current)
        current = res[current]['prev']
    path.reverse()
    if start not in path:
        path = []
    return path



""" Djikstra généralisé : k plus courts chemins """
def k_shortest_paths(graph, s, t, K):
    P = []
    count = {u: 0 for u in graph}
    B = [] 
    heapq.heappush(B, (0, [s])) 
    
    while B and count[t] < K:
        C, path = heapq.heappop(B) 
        u = path[-1] 
        count[u] += 1
        
        if u == t:
            P.append((C, path))
        
        if count[u] <= K:
            for neightbour, w in graph[u].items():
                new_path = path + [neightbour]
                new_cost = C + w
                heapq.heappush(B, (new_cost, new_path))
    
    return P



""" pathA toujours plus court que pathB """
def padding(pathA, pathB):
    diff = len(pathB) - len(pathA)
    for _ in range(diff):
        pathA.append(pathA[-1])
    return pathA, pathB

def couple(pathA, pathB):
    if len(pathA) != len(pathB):
        if len(pathA) > len(pathB):
            pathA, pathB = padding(pathB, pathA)
        else:
            pathB, pathA = padding(pathA, pathB)
    res = []
    for i in range(len(pathA)):
        res.append((pathA[i], pathB[i]))
    return res



def cleanPath(path):
    if len(path) == 0:
        return []
    
    res = [path[0]]
    for i in range(1,len(path)):
        if path[i] != path[i-1]:
            res.append(path[i])
    return res



def exploreDjikstra(graph, start, end, iter=2, path=None, verbose=False):
    res = []
    if path is None:
        path = djikstra(graph, start, end)
        res.append(path)
    else:
        res.append(path)
    i=1 #i=0 est le start
    cpt = 1
    try:
        cpy = deepcopy(graph)
        while iter > 0:
            cpy[path[i]][path[i+1]] = float('inf') #supprime l'arrête
            cpy[path[i+1]][path[i]] = float('inf') #suprrime l'arrête
            new_path = djikstra(cpy, start, end)
            #print(path[i], path[i+1])
            if new_path != [] and new_path not in res:
                iter -= 1
                path = new_path
                res.append(new_path)
                cpy = deepcopy(graph) #reset la copie du graph
            i+=1
    except IndexError:
        if verbose:
            print(f"Pas autant de solution que demandé pour {start} -> {end}")
    finally:
        return res



def noOverlap(pathsA, pathsB):
    pA = []
    pB = []

    for pathA in pathsA:
        a = []
        for vertexA in pathA:
            a.append(vertexA[:-1])
        pA.append(set(a))
    
    for pathB in pathsB:
        b = []
        for vertexB in pathB:
            b.append(vertexB[:-1])
        pB.append(set(b))

    for i in range(len(pA)):
        for j in range(len(pB)):
            if pA[i].intersection(pB[j]) == set():
                return (pathsA[i], pathsB[j])



def resolution(graph, checkpoint, verb=False):
    chemin = []
    for i in range(len(checkpoint)-1):
        Ca = exploreDjikstra(graph, checkpoint[i][0], checkpoint[i+1][0], iter=3, verbose=verb)
        Cb = exploreDjikstra(graph, checkpoint[i][1], checkpoint[i+1][1], iter=3, verbose=verb)
        #print(f"\nChemins trouvés pour {checkpoint[i][0]} -> {checkpoint[i+1][0]} : {Ca}")
        #print(f"Chemins trouvés pour {checkpoint[i][1]} -> {checkpoint[i+1][1]} : {Cb}")
        merge = noOverlap(Ca, Cb)
        #print(f"Solution possible : {merge}\n")
        if merge:
            chemin += couple(merge[1], merge[0])
        else:
            print("Pas de solution trouvée")
            break

    #enlève les doublons
    return cleanPath(chemin)


#Test

if __name__ == "__main__":

    """ #Modélisation du circuit
    graph = dict()
    graph['1L'] = {'1*': 1, '3L': 1}
    graph['1*'] = {'1L': 1}
    graph['1R'] = {'1*': 1}

    graph['2L'] = {'2*': 1, '3L': 1}
    graph['2*'] = {'2L': 1}
    graph['2R'] = {'2*': 1}

    graph['3L'] = {'3*': 1, '7L': 1, '8L': 1}
    graph['3*'] = {'3L': 1, '3R': 1}
    graph['3R'] = {'3*': 1, '4R': 1, '1R': 1, '2R': 1}

    graph['4L'] = {'4*': 1, '3L': 1}
    graph['4*'] = {'4L': 1, '4R': 1}
    graph['4R'] = {'4*': 1, '5R': 1, '6R': 1}

    graph['5L'] = {'5*': 1, '4L': 1}
    graph['5*'] = {'5L': 1, '5R': 1}
    graph['5R'] = {'5*': 1, '7R': 1}

    graph['6L'] = {'6*': 1, '4L': 1}
    graph['6*'] = {'6L': 1, '6R': 1}
    graph['6R'] = {'6*': 1, '7R': 1}

    graph['7L'] = {'7*': 1, '5L': 1, '6L': 1}
    graph['7*'] = {'7L': 1, '7R': 1}
    graph['7R'] = {'7*': 1, '3R': 1}

    graph['8L'] = {'8*': 1}
    graph['8*'] = {'8R': 1}
    graph['8R'] = {'8*': 1, '3R': 1}


    test = {
        'A': {'B': 1, 'C': 2},
        'B': {'A': 1, 'C': 1, 'D': 3},
        'C': {'A':2 ,'D': 1, 'C': 1},
        'D': {'B': 3, 'C': 1}
    } """

    """ print(djikstra(graph, '4*', '8*'))
    paths = k_shortest_paths(graph, '4*', '8*', 10)
    for p in paths:
        print(f"{p[0]} : {p[1]}") """

    """ chemins = exploreDjikstra(graph, '5*', '7R', 3)
    print("Chemins trouvés pour 5* -> 7R :")
    for chemin in chemins:
        print(chemin)

    cheminsB = exploreDjikstra(graph, '4*', '8*', 3)
    print("\nChemins trouvés pour 4* -> 8* :")
    for chemin in cheminsB:
        print(chemin)

    print(f"\nSolution possible : {noOverlap(chemins, cheminsB)}") """

    """ test_graph = dict()
    test_graph['1*'] = {'1R': 1}
    test_graph['1R'] = {'1*': 1, '2R': 1}
    test_graph['1L'] = {'1*': 1}

    test_graph['2*'] = {'2R': 1, '2L': 1}
    test_graph['2R'] = {'2*': 1, '3R': 1, "10R": 1}
    test_graph['2L'] = {'2*': 1, '1L': 1}

    test_graph['3*'] = {'3R': 1, '3L': 1}
    test_graph['3R'] = {'3*': 1, '4R': 1}
    test_graph['3L'] = {'3*': 1, '2L': 1}

    test_graph['4*'] = {'4R': 1, '4L': 1}
    test_graph['4R'] = {'4*': 1, '5R': 1}
    test_graph['4L'] = {'4*': 1, '3L': 1}

    test_graph['5*'] = {'5R': 1, '5L': 1}
    test_graph['5R'] = {'5*': 1, '6R': 1}
    test_graph['5L'] = {'5*': 1, '4L': 1}

    test_graph['6*'] = {'6R': 1, '6L': 1}
    test_graph['6R'] = {'6*': 1, '7R': 1}
    test_graph['6L'] = {'6*': 1, '5L': 1, '8L': 1}

    test_graph['7*'] = {'7L': 1}
    test_graph['7R'] = {'7*': 1}
    test_graph['7L'] = {'7*': 1, '6L': 1}

    test_graph['8*'] = {'8R': 1, '8L': 1}
    test_graph['8R'] = {'8*': 1, '6R': 1}
    test_graph['8L'] = {'8*': 1, '9L': 1}

    test_graph['9*'] = {'9R': 1, '9L': 1}
    test_graph['9R'] = {'9*': 1, '8R': 1}
    test_graph['9L'] = {'9*': 1, '10L': 1}

    test_graph['10*'] = {'10R': 1, '10L': 1}
    test_graph['10R'] = {'10*': 1, '9R': 1}
    test_graph['10L'] = {'10*': 1, '2L': 1}

    checkpoint = [("4*", "5*"), ("8*", "7R"), ("8R", "4*"), ("7*", "4L"),("7*", "3*")]
    checkpoint_ = [("1*", "7*"), ("5R", "10L"), ("7*", "1*")]

    clean = resolution(graph, checkpoint)
    for c in clean:
        print(c) """