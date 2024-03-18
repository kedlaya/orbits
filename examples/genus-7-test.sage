import itertools

F = GF(2)
G = SO(10,2,e=1)
J = G.invariant_form()
J1 = block_matrix(2,2, [0, identity_matrix(F, 5), identity_matrix(F, 5), 0], subdivide=False)
Pg = SymmetricGroup(10)([(2,6,8,9,5,3),(4,7)])
l1 = []
for g in G.gens():
    M = copy(g.matrix())
    M.permute_rows_and_columns(~Pg, ~Pg)
    assert M*J1*M.transpose() == J1
    l1.append(M)
G0 = GL(10, F).subgroup(l1)
assert all(g*J1*g.matrix().transpose() == J1 for g in G0.gens())

l2 = [identity_matrix(10, F)]
l2[0][3,9] = 1
l2[0][4,8] = 1
l2.append(Matrix(F, [[0,1,0,0,0,1,0,0,1,0],
                     [0,0,0,1,1,0,1,1,0,0],
                     [0,1,0,0,0,1,0,1,0,1],
                     [1,0,1,0,1,0,1,1,0,1],
                     [0,1,0,1,1,0,1,0,1,0],
                     [0,0,1,0,0,0,1,0,0,1],
                     [1,1,0,1,1,0,0,0,0,0],
                     [0,0,0,0,1,0,0,1,0,0],
                     [0,1,0,0,0,1,0,1,1,0],
                     [1,0,0,1,1,0,0,1,0,0]]))
G1 = G0.subgroup(l2)
assert G0.order() // G1.order() == 2

def apply_group_elem(g, M):
    M1 = M*g.transpose() # Result is mutable
    M1.echelonize()
    return as_immutable(M1)
    
def optimized_rep(g):
    return g.matrix()

M0 = as_immutable(block_matrix(1, 2, [identity_matrix(F, 5), Matrix(F,5)], subdivide=False))
assert M0.echelon_form() == M0

retract = CayleyGroupRetract(G1, [M0], apply_group_elem, optimized_rep)
vertices = list(retract.keys())

use_forbid = True

if use_forbid:
    P.<x0,x12,x13,x14,x15,x23,x24,x25,x34,x35,x45,x1234,x1235,x1245,x1345,x2345> = PolynomialRing(F, 16)
    quads = [x0*x2345 + x23*x45 + x24*x35 + x25*x34,
         x12*x1345 + x13*x1245 + x14*x1235 + x15*x1234,
         x0*x1345 + x13*x45 + x14*x35 + x15*x34,
         x12*x2345 + x23*x1245 + x24*x1235 + x25*x1234,
         x0*x1245 + x12*x45 + x14*x25 + x15*x24,
         x13*x2345 + x23*x1345 + x34*x1235 + x35*x1234,
         x0*x1235 + x12*x35 + x13*x25 + x15*x23,
         x14*x2345 + x24*x1345 + x34*x1245 + x45*x1234,
         x0*x1234 + x12*x34 + x13*x24 + x14*x23,
         x15*x2345 + x25*x1345 + x35*x1245 + x45*x1235]

    def spinor_coordinates(M):
        coord1 = [_ for i in [0,2,4] for _ in itertools.combinations(range(5), i)]
        coord2 = [_ for i in [1,3,5] for _ in itertools.combinations(range(5), i)]
        ops = []
        # Annihilation operators.
        for i in range(5):
            ops.append(Matrix(F, 16, 16, [[1 if 
                i not in coord2[k] and set(coord2[k]).union(set([i])) == set(coord1[j]) 
                else 0 for k in range(16)] for j in range(16)]))
        # Creation operators.
        for i in range(5):
            ops.append(Matrix(F, 16, 16, [[1 if 
                i not in coord1[j] and set(coord1[j]).union(set([i])) == set(coord2[k]) 
                else 0 for k in range(16)] for j in range(16)]))
        ans = {}
        for m in M:
            l = [sum(ops[j]*m[i,j] for j in range(10)) for i in range(5)]
            foo = Matrix(itertools.chain.from_iterable(N.rows() for N in l))
            K = foo.right_kernel()
            assert K.dimension() == 1
            v = K.gens()[0]
            ans[m] = as_immutable(v)
        return ans

    coords = spinor_coordinates(vertices)

    def linear_section(coords, P=P, quads=quads):
        V = Matrix(coords).right_kernel()
        tmp2 = [sum(P.gens()[i] * v[-1-i] for i in range(16)) for v in V.gens()] + quads
        return P.ideal(tmp2)

    def forbid(mats, coords=coords):
        if len(mats) == 2:
            vecs = [M.row_space() for M in mats]
            if vecs[0].intersection(vecs[1]).dimension() != 1:
                return True
        tmp = [coords[M] for M in mats]
        if len(mats) == 3:
            if Matrix(tmp).rank() < 3:
                return True
        if len(mats) == 4:
            if Matrix(tmp).rank() < 4:
                return True
        if len(mats) == 5:
            J = linear_section(tmp)
            if J.dimension() > 1:
                 return True
        return False
else:
    forbid = None

methods = {'action': apply_group_elem,
           'optimized_rep': optimized_rep,
           'forbid': forbid}
           
tree = OrbitLookupTree(G1, vertices, methods)
tree.extend(6, verbose=True)

