#cd desktop/"casser des graphes"/"Park and Philips algorithm"
#!/usr/bin/env sage -python

import os
import networkx as nx
from djikstra_park_and_phillips import *
from sage.all import *
import time,random

os.chdir("/users/antoine/desktop/casser des graphes/Park and Philips algorithm")

def dual_graph(G_primal,dico_node_weight):
    faces = G_primal.faces()
    dico_faces={}
    dico_edge_dual={}
    dico_node_face={}
    dico_edge_face={}
    add_weight_to_face_with_edge=[]
    faces_dual=[]
    G_dual=Graph()
    node=1
    
    for face in faces:
        G_dual.add_vertex(node)
        dico_faces[tuple(face)]=node
        node+=1
    for edge in G_primal.edges():
        u,v,cost = edge
        dual_vertices=[]
        for face in faces:
            if (u,v) in face or (v,u) in face:
                dual_vertices.append(face)
        if len(dual_vertices) == 2:
            face_1 = dico_faces[tuple(dual_vertices[0])]
            face_2 = dico_faces[tuple(dual_vertices[1])]
            dual_edge = (face_1,face_2)
            
            if not((face_1,face_2) in G_dual.edges() or (face_2,face_1) in G_dual.edges()):
                G_dual.add_edge(face_1,face_2,cost)
                
            dico_edge_dual[dual_edge]=(edge,cost)
            dico_edge_dual[(dual_edge[1],dual_edge[0])]=(edge,cost)
            for node in [u,v]:
                if not node in dico_node_face.keys():
                    dico_node_face[node]=[]
                if (face_1,face_2) in dico_node_face[node] or (face_2,face_1) in dico_node_face[node]:
                    dico_node_face.pop(node)
                    add_weight_to_face_with_edge.append((dual_edge,dico_node_weight[node]["weight"]))
                else:
                    dico_node_face[node].append(dual_edge)
                    if not dual_edge in dico_edge_face.keys():
                        dico_edge_face[dual_edge]=[]
                    dico_edge_face[dual_edge].append(node)
    for dual_edge,weight_node in add_weight_to_face_with_edge:
        node = dico_edge_face[dual_edge][0]
        dico_node_weight[node]["weight"]+=weight_node
    G_dual.is_planar(set_embedding=True)
    if len(G_dual.edges()) >= 3:
        edges_tree = sage.graphs.spanning_tree.random_spanning_tree(G_dual)
    else:
        edges_tree = G_dual.edges()
    edges_tree_with_weight=[]
    for edge in edges_tree:
        edges_tree_with_weight.append((edge[0],edge[1],dico_edge_dual[edge][1]))
    
    return G_dual,G_dual.get_embedding(),edges_tree_with_weight,dico_node_face,dico_node_weight,dico_edge_dual

def largest_conn_comp(G_primal):
    #return the largest connected component of the connected components of the graph
    connected_components = G_primal.connected_components()
    max_size=0
    i=0
    for comp in connected_components:
        if len(comp)>max_size:
            max_size=len(comp)
            i_max=i
        i+=1
    largest_connected_component = connected_components[i_max]
    edges_to_delete = []
    vertices_to_delete = []
    i=0
    for comp in connected_components:
        if i!=i_max:
            G_primal.delete_vertices(comp)
        i+=1
    return G_primal

def get_outer_edges_root(G,faces,embedding,edges_tree):
    list_face_length = sorted(faces, key=lambda x: len(x),reverse=True)
    outer_face=[]
    stop=False
    i=0
    while i<len(list_face_length) and not stop:
        face = list_face_length[i]
        i+=1
        
        already_visited_vertex = []
        vertex,vertex_parent = face[0]
        size = -1
        while not vertex in already_visited_vertex and size!=-2:
            embedding_vertex = order_edges_embedding(vertex,vertex_parent,embedding)
            found_next_vertex = False
            j=0
            for w in embedding_vertex:
                if not found_next_vertex and ((vertex,w) in face or (w,vertex) in face):
                    vertex_parent = vertex
                    vertex = w
                    found_next_vertex = True
                j+=1
            already_visited_vertex.append(vertex)
            if size == -1:
                if j==0:
                    size=0
                elif j==len(embedding_vertex):
                    size=1
                else:
                    size=-2
            elif size==0 and j!=0:
                size=-2
            elif size==1 and j!=len(embedding_vertex):
                size=-2
                
        if size!=-2:
            stop=True
            outer_face = face
    #print("outer face : ")
    #print(outer_face) 
    
    dico={}
    for u,v in outer_face:
        if not u in dico.keys():
            dico[u]=[]
        if not v in dico.keys():
            dico[v]=[]
        dico[u].append(v)
        dico[v].append(u)
                
    root,left_outer_edge,right_outer_edge = (-1,-1,-1)
    neighbor_1 = -1
    neighbor_2 = -1
    stop = False
    i=0
    while outer_face  != [] and i<len(outer_face) and root == -1:
        
        u,v = outer_face[i]
        i+=1  
        if G.degree(u)>=3:
            root = u
            neighbor_1 = dico[root][0]
            neighbor_2 = dico[root][1]
        elif G.degree(v)>=3:
            root = v
        
        if root !=-1:
            
            embedding_vertex_1 = order_edges_embedding(root,neighbor_1,embedding)
            embedding_vertex_2 = order_edges_embedding(root,neighbor_2,embedding)
            
            if embedding_vertex_1[0]==neighbor_2:
                left_outer_edge = (root,neighbor_1)
                right_outer_edge = (root,neighbor_2)
            elif embedding_vertex_2[0]==neighbor_1:
                left_outer_edge = (root,neighbor_2)
                right_outer_edge = (root,neighbor_1)

    if root != -1:
        
        G_edges_tree = Graph(edges_tree)
        
        edge_neighbor_1 = (root,neighbor_1,G.edge_label(root,neighbor_1))
        edge_neighbor_2 = (root,neighbor_2,G.edge_label(root,neighbor_2))
        
        if G_edges_tree.has_edge(root,neighbor_1):
            G_edges_tree.delete_edge(root,neighbor_1)
        if not G_edges_tree.has_edge(root,neighbor_2):
            G_edges_tree.add_edge(edge_neighbor_2[0],edge_neighbor_2[1],edge_neighbor_2[2])
        all_paths_root_1 = G_edges_tree.all_paths(neighbor_1,root)
        for path in all_paths_root_1:
            G_edges_tree.delete_edge(path[0],path[1])
            
        if G_edges_tree.has_edge(root,neighbor_2):
            G_edges_tree.delete_edge(root,neighbor_2)
        if not G_edges_tree.has_edge(root,neighbor_1):
            G_edges_tree.add_edge(edge_neighbor_1[0],edge_neighbor_1[1],edge_neighbor_1[2])
        all_paths_root_2 = G_edges_tree.all_paths(neighbor_2,root)
        for path in all_paths_root_2:
            G_edges_tree.delete_edge(path[0],path[1])
        
        if not G_edges_tree.has_edge(root,neighbor_2):
            G_edges_tree.add_edge(edge_neighbor_2[0],edge_neighbor_2[1],edge_neighbor_2[2])
        if not G_edges_tree.has_edge(root,neighbor_1):
            G_edges_tree.add_edge(edge_neighbor_1[0],edge_neighbor_1[1],edge_neighbor_1[2])
            
    return root,left_outer_edge,right_outer_edge,outer_face,G_edges_tree.edges()
      
def order_tree(root,edges_tree):
    dico_childrens={root:[]}
    cpt_edges_ordered = 0
    while cpt_edges_ordered < len(edges_tree):
        for edge in edges_tree:
            if len(edge)==2:
                u,v=edge
            else:
                u,v,_=edge
            if u in dico_childrens.keys() and not v in dico_childrens.keys():
                dico_childrens[u].append(v)
                dico_childrens[v]=[]
                cpt_edges_ordered+=1
            elif v in dico_childrens.keys() and not u in dico_childrens.keys():
                dico_childrens[v].append(u)
                dico_childrens[u]=[]
                cpt_edges_ordered+=1
    return dico_childrens

def order_edges_embedding(node, node_parent,embedding):
    index_parent = embedding[node].index(node_parent)
    
    list_edges_ordered = []
    j=1
    for node_adj in embedding[node][:-1]:
        list_edges_ordered.append(embedding[node][(index_parent+j)%len(embedding[node])])
        j+=1
    return list_edges_ordered
    
def labelling_of_regions_spanning_tree(dico_childrens_tree,embedding,root,left_outer_edge,right_outer_edge):
    current_node = root
    nodes_already_visited = []
    dico_parents = {} #dictionnary node:parent in the tree
    last_node = -1
    next_node = -1
    current_label = 1
    label_of_regions = {} #node : regions
    stop=False
    
    while not root in nodes_already_visited:
        #print(len(label_of_regions))
        childrens_current_node = dico_childrens_tree[current_node]
        if current_node != root:
            emb = order_edges_embedding(current_node,dico_parents[current_node],embedding)
            embedding_current_node_ordered = emb.copy()
            embedding_current_node_ordered.reverse()
        else:
            v = right_outer_edge[0] if right_outer_edge[0]!=root else right_outer_edge[1]
            embedding_current_node_ordered = order_edges_embedding(current_node,v,embedding)
            embedding_current_node_ordered.reverse()
            embedding_current_node_ordered.append(v)
        next_node = -1
        if not current_node in label_of_regions.keys():
            label_of_regions[current_node]=[]
        for node in embedding_current_node_ordered:
            if node in childrens_current_node:
                dico_parents[node]=current_node                
            if node in childrens_current_node and next_node==-1 and not node in nodes_already_visited:
                next_node = node
                if last_node==-1:
                    last_node = next_node
                    #label_of_regions[current_node].append(([left_outer_edge,right_outer_edge],current_label))
                #else:
                label_of_regions[current_node].append(([(last_node,current_node),(current_node,next_node)],current_label))
                current_label+=1
                    
        if next_node == -1:
            nodes_already_visited.append(current_node)
            if current_node != root:
                next_node = dico_parents[current_node]
                if last_node != dico_parents[current_node]:
                    label_of_regions[current_node].append(([(last_node,current_node),(current_node,next_node)],current_label))
                else:
                    label_of_regions[current_node].append(([(next_node,current_node)],current_label))
                current_label+=1
        #print("current_node : "+str(current_node))
        #print("next_node : "+str(next_node))
        #print("last_node : "+str(last_node))
        
        last_node = current_node
        current_node = next_node
    return label_of_regions
           
def spanning_tree(G_dual,embedding,edges_tree,root,left_outer_edge,right_outer_edge):
    tree_ordered={} #parent:childrens
    #we order the spanning tree according to the root
    dico_childrens_tree = order_tree(root,edges_tree,{})
    label_of_regions = labelling_of_regions_spanning_tree(dico_childrens_tree,root,left_outer_edge,right_outer_edge)
    
    return dico_parents_tree,label_of_regions

def get_regions_embedded(edge,labelling,embedding,edges_tree):
    edges_tree_without_weight = [(edge[0],edge[1]) for edge in edges_tree]
    u,v,label = edge
    cost = 0
    in_tree = True
    #cost = label['weight']
    cost = label
    if (u,v,label) in edges_tree or (v,u,label) in edges_tree:
        return (in_tree,cost,None)
    else:
        in_tree=False
        region_u = -1
        region_v = -1
        regions = []
        for vertex in [u,v]:
            if vertex == u:
                other_vertex = v
            else:
                other_vertex = u
                
            labels_vertex = labelling[vertex]
            if len(labels_vertex)==1:
                region_vertex = labels_vertex[0][1]
            else:
                region_vertex = -1
                for list_n,label in labels_vertex:
                    if region_vertex == -1:
                        n1,n2 = list_n[0]
                        n3,n4 = list_n[1]
                        embedding_vertex = order_edges_embedding(vertex,n1,embedding)
                        in_the_zone = True
                        rectification = False
                        for node_adjacent_to_vertex in embedding_vertex:
                            if (node_adjacent_to_vertex,vertex) in edges_tree_without_weight or (vertex,node_adjacent_to_vertex) in edges_tree_without_weight:
                                if in_the_zone:
                                    rectification = True
                                    region_vertex = -1
                            if node_adjacent_to_vertex==n4:
                                in_the_zone = not in_the_zone
                            if node_adjacent_to_vertex == other_vertex:
                                if in_the_zone and not rectification:
                                    region_vertex = label
                                if not in_the_zone and rectification:
                                    region_vertex = label
            regions.append(region_vertex)
        return (in_tree,cost,regions)  
    
def get_edges_enclosed_in_cycle(edge,list_vertices_cycle,dual_embedding):
    list_edges_enclosed = []
    u,v = edge
    vertices_to_explore = [] 
    inner_edges = []
    outer_edges = []
    #print("vertices cycle : ")
    #print(list_vertices_cycle)
    #print("edge : ")
    #print(edge)
    
    already_visited = []
    previous_vertex = u
    #exploring the vertices of the cycle
    n = len(list_vertices_cycle)
    for i in range(n):    
        vertex = list_vertices_cycle[i]
        next_vertex = list_vertices_cycle[(i+1)%n]
        list_nei = order_edges_embedding(vertex,previous_vertex,dual_embedding)
        list_neighbors_ordered = list_nei.copy()
        list_neighbors_ordered.reverse()
        
        #print(previous_vertex,vertex,list_neighbors_ordered)
        in_the_zone = False
        #print("vertex : "+str(vertex))
        for neighbor in list_neighbors_ordered:#[::-1]:
            #print("neighbor et in_the_zone : ")
            #print(neighbor,in_the_zone)
            if neighbor == next_vertex:
                in_the_zone = True
            elif in_the_zone:
                if not neighbor in vertices_to_explore and not neighbor in list_vertices_cycle:
                    vertices_to_explore.append(neighbor)
                if not (vertex,neighbor) in list_edges_enclosed and not (neighbor,vertex) in list_edges_enclosed:
                    list_edges_enclosed.append((vertex,neighbor))
                    inner_edges.append((vertex,neighbor))
                    
        list_edges_enclosed.append((vertex,previous_vertex))
        already_visited.append(vertex)
        outer_edges.append((vertex,previous_vertex))
        previous_vertex = vertex
    #print("after cycle")
    #print(vertices_to_explore)
    #after exploring the vertices of the cycle
    while len(vertices_to_explore)!=0 :
        vertex = vertices_to_explore[0]
        list_neighbors_ordered = dual_embedding[vertex]
        for neighbor in list_neighbors_ordered:
            if not (vertex,neighbor) in list_edges_enclosed and not (neighbor,vertex) in list_edges_enclosed:
                list_edges_enclosed.append((vertex,neighbor))
                inner_edges.append((vertex,neighbor))
                if not neighbor in vertices_to_explore and not neighbor in already_visited:
                    vertices_to_explore.append(neighbor)
        vertices_to_explore.remove(vertex)
        already_visited.append(vertex)
    
    #print("edges enclosed : ")
    #print(edge,list_edges_enclosed)
    return list_edges_enclosed,inner_edges,outer_edges

def get_dico_face_node_weight(dico_node_face,dico_node_weight,outer_face):
    print("OUTER FACE : ")
    print(outer_face)
    dico_face_node_weight={}
    for node,face in dico_node_face.items():
        if set(face)!=set(outer_face):
            dico_face_node_weight[tuple(face)]=dico_node_weight[node]['weight']
    return dico_face_node_weight

def get_weight_enclosed_in_cycle(edge,list_vertices_cycle,dual_embedding,dico_face_node_weight,G_dual,dico_weight_enclosed): 
    list_edges_enclosed,inner_edges,outer_edges = get_edges_enclosed_in_cycle(edge,list_vertices_cycle,dual_embedding)
    #print(edge)
    #print("inner edges : "+str(inner_edges))
    #print("outer edges : "+str(outer_edges))
    weight_enc_max = 0
    edges_removed_outer = []
    edges_removed_enclosed = []
    for edge1 in list_edges_enclosed:
        if edge1 in dico_weight_enclosed.keys():
            weight_enc,inner_edges1,outer_edges1 = dico_weight_enclosed[edge1]
            if weight_enc_max < weight_enc:
                weight_enc_max = weight_enc
                inner_edges_max = inner_edges1.copy()
                outer_edges1_max = outer_edges1.copy()
    if weight_enc_max>0:
        for u,v in list_edges_enclosed.copy():
            if (u,v) in inner_edges_max or (v,u) in inner_edges_max:
                list_edges_enclosed.remove((u,v))
                if (v,u) in list_edges_enclosed:
                    list_edges_enclosed.remove((v,u))
                edges_removed_enclosed.append((u,v))
                
            elif ((u,v) in outer_edges1_max or (v,u) in outer_edges1_max) and ((u,v) in outer_edges or (v,u) in outer_edges):
                list_edges_enclosed.remove((u,v))
                if (v,u) in list_edges_enclosed:
                    list_edges_enclosed.remove((v,u))
                edges_removed_outer.append((u,v))
    #print(" ")
    #print("edges_removed_enclosed : "+str(edges_removed_enclosed))
    #print("edges_removed_outer : "+str(edges_removed_outer))
    sum_weight = weight_enc_max
    faces_enclosed = []
    for face,weight in dico_face_node_weight.items():
        k=0
        i=0
        while i < len(face) and k==0:
            u,v = face[i]
            i+=1
            if not (u,v) in list_edges_enclosed and not  (v,u) in list_edges_enclosed:
                k=1
        if k==0:
            sum_weight+=weight
            faces_enclosed.append(face)
    #print(edge)
    #print("face enclosed : ")
    #print(faces_enclosed)
    #print("weight enclosed : "+str(sum_weight))
    return sum_weight,inner_edges,outer_edges

    
def creation_of_Gs(G_dual,dual_embedding,labelling,edges_tree,dico_node_face,dico_node_weight,outer_face):
    Gs = DiGraph(multiedges=True)
    dico_face_node_weight = get_dico_face_node_weight(dico_node_face,dico_node_weight,outer_face)
    tree = Graph()
    tree.add_edges(edges_tree)
    list_edges_dual = G_dual.edges(sort=False)
    dico_weight_enclosed={}
    for edge in list_edges_dual:
        u,v,label = edge
        in_tree,cost,regions = get_regions_embedded(edge,labelling,dual_embedding,edges_tree)
        if in_tree :
            label1 = (cost,0)
            label2 = (cost,0)
        else:
            region_u = regions[0]
            region_v = regions[1]
            
            
            if region_u < region_v:
                list_vertices_cycle = tree.shortest_path(v,u)
                w_uv,inner_edges,outer_edges = get_weight_enclosed_in_cycle((u,v),list_vertices_cycle,dual_embedding,dico_face_node_weight,G_dual,dico_weight_enclosed)
                
                label1 = (cost,w_uv)
                label2 = (cost,-w_uv)
                w = w_uv
            else:
                list_vertices_cycle = tree.shortest_path(u,v)
                w_vu,inner_edges,outer_edges = get_weight_enclosed_in_cycle((v,u),list_vertices_cycle,dual_embedding,dico_face_node_weight,G_dual,dico_weight_enclosed)
                
                label1 = (cost,-w_vu)
                label2 = (cost,w_vu)
                
                w = w_vu
            dico_weight_enclosed[(u,v)] = (w,inner_edges,outer_edges)
            dico_weight_enclosed[(v,u)] = (w,inner_edges,outer_edges)
            
        Gs.add_edges([(u,v,label1),(v,u,label2)]) 
        
    return Gs
        
def create_expanded_Gs(Gs,W):
    expanded_Gs = DiGraph(multiedges=True)
    for edge in Gs.edges():
        u,v,label = edge
        cost = label[0]["weight"]
        w_uv = label[1]
        lower_bound = max(-W,-W-w_uv)
        upper_bound = min(W,W-w_uv) 
        expanded_Gs.add_edges([(str(u)+"_"+str(w),str(v)+"_"+str(w+w_uv),cost) for w in range(lower_bound,upper_bound+1)])
        
    return expanded_Gs

def pseudo_quotient(weight_path,cost_path,edge_v_u,W):
    sum_weight = weight_path
    sum_cost = cost_path
    
    v,u,label = edge_v_u
    sum_cost += label[0]["weight"]
    sum_weight += label[1]

    if min(abs(sum_weight),W-abs(sum_weight)) == 0:
        return 10^6
    return sum_cost/min(abs(sum_weight),W-abs(sum_weight))


def create_table_T(expanded_Gs,Gs,W,dico_edge_dual,epsilon=0,stop_cost=0):
    print("computing of the table stop with cost of cut inferior to "+str(stop_cost))
    table = {}
    cpt = 0
    min_pseudo_quot = 10^6
    min_cost_cut = 10^6
    list_edges_Gs = Gs.edges()
    i=0
    stop=False
    
    if epsilon == 0 and W%2 == 1:
        epsilon = 1/W
    lowerb =  W/2-epsilon*W
    upperb = W/2+epsilon*W
    print("To improve the computing time, we won't compute all the cycles in expanded_Gs, ")
    print("only the cycle that enclose a weight between "+str(lowerb)+" and "+str(upperb))

    while i < len(list_edges_Gs) and not stop:
        edge = list_edges_Gs[i]
        i+=1
        u,v,label = edge
        w_uv = label[1]
        if not u in table.keys():
            table[u]={}
        if not v in table[u].keys():
            table[u][v]={}
        
        
        dico_paths = dijkstra_park_phillips(expanded_Gs,v,u,W,w_uv,epsilon)
        for weight_path,elems in dico_paths.items():
            cost_path,path,path_edge = elems
            #print(path)
            #print(path_edge)
            pseudo_quot = pseudo_quotient(weight_path,cost_path,edge,W)
            w = weight_path+w_uv
            
            _,_,label = edge
            c = cost_path+label[0]["weight"]
            if c <= stop_cost:
                stop=True
            table[u][v][w] = (path,pseudo_quot)
            cpt+=1
            if min_pseudo_quot > pseudo_quot:
                min_pseudo_quot = pseudo_quot
                min_path = path
    cutset,cost_cut = get_cut_in_primal_graph(min_path,dico_edge_dual)    
    print("number of paths computed in expanded_Gs : "+str(cpt))
    return table,cutset,cost_cut,min_pseudo_quot,min_path

def get_cut_in_primal_graph(min_path,dico_edge_dual):
    cutset=[]
    cost_cut=0
    u = min_path[0]
    first_vertex = min_path[0]
    for v in min_path[1:]:
        u_dual = int(u.split("_")[0])
        v_dual = int(v.split("_")[0])
        u_primal,v_primal,label = dico_edge_dual[(u_dual,v_dual)][0]
        
        cutset.append((u_primal,v_primal))
        cost_cut+=label['weight']
        
        u=v
    
    u_dual = int(v.split("_")[0])
    v_dual = int(first_vertex.split("_")[0])
    u_primal,v_primal,label = dico_edge_dual[(u_dual,v_dual)][0]
    
    cutset.append((u_primal,v_primal))
    cost_cut+=label['weight']
    
    return cutset,cost_cut
    
        
        
def get_W(primal_graph):
    W=0
    for node,weight in primal_graph.nodes(data=True):
        W+=weight["weight"]
    return W   
        
def create_Gs(primal_graph):
    #we keep only the largest connected component, because otherwise the dual graph method doesn't work well
    G_primal = largest_conn_comp(Graph(primal_graph))
    dico_node_weight = primal_graph.nodes(data=True)
    print("computing of the dual Graph : ")
    G_dual,dual_embedding,edges_tree,dico_node_face,dico_node_weight,dico_edge_dual = dual_graph(G_primal,dico_node_weight)
    print("        number of nodes of the dual graph : "+str(len(G_dual.vertices())))
    print("        number of edges of the dual graph : "+str(len(G_dual.edges())))
    dual_faces = list(dico_node_face.values())
    root,left_outer_edge,right_outer_edge,outer_face,edges_tree = get_outer_edges_root(G_dual,dual_faces,dual_embedding,edges_tree)
    #edges_tree = [(1, 3, {'weight': 2}), (1, 4, {'weight': 2}), (2, 4, {'weight': 2}), (3, 6, {'weight': 2}), (4, 5, {'weight': 2})]
    #root = 1
    #left_outer_edge = (1,4)
    #right_outer_edge = (1,3)
    dico_childrens = order_tree(root,edges_tree)
    print("labelling of the spanning tree of the dual : ")
    labelling = labelling_of_regions_spanning_tree(dico_childrens,dual_embedding,root,left_outer_edge,right_outer_edge)
    #print(labelling) 
    print("Creation of Gs : ")
    Gs = creation_of_Gs(G_dual,dual_embedding,labelling,edges_tree,dico_node_face,dico_node_weight,outer_face)
    print("        number of nodes of Gs : "+str(len(Gs.vertices())))
    print("        number of edges of Gs : "+str(len(Gs.edges())))
    return Gs,G_dual,dual_embedding,edges_tree,dico_edge_dual



