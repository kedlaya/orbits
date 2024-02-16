# Legacy interface for backward compatibility
load("orbits.sage")

def build_orbit_tree(G, S, n, methods, verbose=True, terminate=True):    
    tree = OrbitLookupTree(G, S, methods)
    tree.extend(n, verbose)
    return tree

def green_nodes(tree, n):
    return list(tree.green_nodes(n))

def orbit_rep_from_tree(G, tree, mats, apply_group_elem=None, optimized_rep=None, find_green=True):
    return tree.orbit_rep(mats)

