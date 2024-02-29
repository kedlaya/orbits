# This example computes orbit representatives for the action of GL(5, F_2) on subspaces
# of \bigvee^2 F_2^5. This can be used to classify curves or K3 surfaces of genus 6 over F_2.

# Construct group generators.
F = GF(2)
G0 = SymmetricGroup(10)
g1 = G0([(1,5,8,10,4),(2,6,9,3,7)]).matrix().change_ring(F)
g2 = identity_matrix(F, 10)
g2[1,4] = 1
g2[2,5] = 1
g2[3,6] = 1
G = MatrixGroup([g1,g2])

def optimized_rep(g):
    return g.matrix()

methods = {'action': lambda g, x: as_immutable(g*x),
           'optimized_rep': optimized_rep}

S = VectorSpace(F, 10)
tree = LinearOrbitLookupTree(G, S, methods)
tree.extend(4, verbose=True)

# Print stabilizers at level 3
for mats in tree.orbit_reps(3):
    print(tree.stabilizer(mats))
