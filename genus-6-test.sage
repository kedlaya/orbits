load("orbits.sage")

# Construct generators for GL(5,F_2) acting on \bigvee^2 F_2^5
F = GF(2)
G0 = SymmetricGroup(10)
g1 = G0([(1,5,8,10,4),(2,6,9,3,7)]).matrix().change_ring(F)
g2 = identity_matrix(F, 10)
g2[1,4] = 1
g2[2,5] = 1
g2[3,6] = 1
G = MatrixGroup([g1,g2])

# Construct an orbit lookup tree of depth 4 for the action of G on the dual of P^9
def optimized_rep(g):
    return g.matrix()

methods = {'action': mult_immutable,
           'optimized_rep': optimized_rep}

S = VectorSpace(F, 10)
tree = OrbitLookupTree(G, S, methods, linear=True)
tree.extend(4, verbose=True)

