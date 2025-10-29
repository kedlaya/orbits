import itertools

F = GF(3)
P.<x0,x1,x2,x3,x4> = F[]
monos2 = [P.gens()[i]*P.gens()[j] for i in range(5) for j in range(i, 5)]
G0 = SL(5, F)
l = []
for g in G0.gens():
    mat = []
    for mu in monos2:
        mu2 = mu(*(sum(g.matrix()[i,j]*P.gens()[i] for i in range(5)) for j in range(5)))
        mat.append([mu2.coefficient(mu3) for mu3 in monos2])
    l.append(Matrix(F, mat).transpose())
G = MatrixGroup(l)
assert G.order() == G0.order()

methods = {'action': lambda g, x: as_immutable(g*x),
           'optimized_rep': lambda g: g.matrix()}

S = VectorSpace(F, 15)
tree = LinearOrbitLookupTree(G, S, methods, check_closure=False)
tree.extend(2, verbose=True)

