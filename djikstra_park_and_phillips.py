import os
from heapq import heappop,heappush
from sage.all import *

os.chdir("/users/antoine/desktop/casser des graphes/Park and Philips algorithm")
def voisins (expanded_Gs,s):
    outg_ed =  expanded_Gs.outgoing_edges(s)
    return [(cost,v) for u,v,cost in outg_ed]

def dijkstra(expanded_Gs,name_s, name_t):
    cost = expanded_Gs.edge_label(name_s,name_t)[0]
    expanded_Gs.delete_edge(name_s,name_t)
    
    dico_paths = {}
    M = set()
    d = {name_s: 0}
    p = {}
    suivants = [(0, name_s)] 
    while suivants != [] and not name_t in M:
        
        dx, x = heappop(suivants)
        
        if x in M:
            continue
    
        M.add(x)

        for w, y in voisins(expanded_Gs,x):
            if y in M:
                continue
            dy = dx + w
            if y not in d or d[y] > dy:
                d[y] = dy
                heappush(suivants, (dy, y))
                p[y] = x
                
    expanded_Gs.add_edge(name_s,name_t,cost)  
            
    path = [name_t]
    path_edge=[]
    y=name_t
    x = name_t
    while x != name_s:
        x = p[x]
        path.insert(0, x)
        path_edge.insert(0,(x,y))
        y=x
    path_edge.append((name_t,name_s))
    return d[name_t],path,path_edge
                
def dijkstra_park_phillips(expanded_Gs,s,t,W,w_uv,epsilon=0):
    epsilon = max(0,min(epsilon,0.5))
        
    dico_paths = {}
    name_s = str(s)+"_0"
    M = set()
    d = {name_s: 0}
    p = {}
    list_name_t = []
    suivants = [(0, name_s)] 
    stop = False
    
    set_of_destinations = []
    for weight in range(1,W+1):
        weight_of_cut = weight+w_uv
        name_t = str(t)+"_"+str(weight)
        if weight_of_cut >= W/2-epsilon*W and weight_of_cut <= W/2 + epsilon*W:
            set_of_destinations.append(name_t)
    while suivants != [] and not stop:
        
        dx, x = heappop(suivants)
        
        if x in M:
            continue
    
        M.add(x)
        
        stop=True
        for dest in set_of_destinations:
            if not dest in M:
                stop=False

        for cost, y in voisins(expanded_Gs,x):
            
            elems = y.split("_")
            if int(elems[0])==t:
                if y in set_of_destinations:
                    list_name_t.append((y,int(elems[1])))
            if y in M:
                continue
            dy = dx + cost
            if y not in d or d[y] > dy:
                d[y] = dy
                heappush(suivants, (dy, y))
                p[y] = x
                
    for name_t,weight in list_name_t:
        path_edge=[]
        y=name_t
        path = [name_t]
        x = name_t
        while x != name_s:
            x = p[x]
            path.insert(0, x)
            path_edge.insert(0,(x,y))
            y=x
        path_edge.append((name_t,str(s)+"_"+str(w_uv+weight)))

        if len(path)==2:
            dico_paths[weight]=dijkstra(expanded_Gs,name_s, name_t)
        else:
            dico_paths[weight]=(d[name_t],path,path_edge)
    return dico_paths

