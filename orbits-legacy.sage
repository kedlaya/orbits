# Legacy interface for backward compatibility
load("orbits.sage")

def build_orbit_tree(G, S, n, methods, verbose=True, terminate=True):
    if 'action' not in methods:
        methods['action'] = methods['apply_group_elem']
    tree = OrbitLookupTree(G, S, methods)
    tree.extend(n, verbose)
    return tree

def green_nodes(tree, n):
    return list(tree.orbit_reps(n))

def orbit_rep_from_tree(G, tree, mats, apply_group_elem=None, optimized_rep=None, find_green=True):
    return tree.orbit_rep(mats)

def vec_stab(M, transpose=False):
    """
    Compute the stabilizer of a subspace of a vector space.
    
    INPUT:
    
     - ``M`` -- a matrix over a field
     
     - ``transpose`` -- a boolean (default `False`)
     
    OUTPUT: 
    
    The subgroup of `GL(n,F)`` stabilizing the subspace defined by the rows of `M` 
    for the right action (if ``transpose`` is `False`) or the left action (otherwise).
    """
    F = M.base_ring()
    m,n = M.dimensions()
    # Conjugate to a standard matrix.
    l = M.rows()
    for i in range(n):
        if i not in M.pivots():
            l.append(vector(F, (1 if j==i else 0 for j in range(n))))
    M1 = Matrix(F, l)
    # Then construct a block matrix group.
    l0 = [block_matrix(2,2,[g.matrix(),0,0,identity_matrix(n-m)], subdivide=False) for g in GL(m, F).gens()] + \
        [block_matrix(2,2,[identity_matrix(m),0,0,g.matrix()], subdivide=False) for g in GL(n-m, F).gens()]
    l0.append(identity_matrix(n))
    l0[-1][m,0] = 1
    if transpose:
        G = GL(n, F).subgroup([(~M1*g*M1).transpose() for g in l0])
    else:
        G = GL(n, F).subgroup([~M1*g*M1 for g in l0])
        assert all((M*g.matrix()).echelon_form() == M.echelon_form() for g in G.gens())
    return G


