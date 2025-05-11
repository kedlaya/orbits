load("orbits.sage")
import itertools

n = 2
genus = 4

F2 = GF(2)
F.<a> = GF(2^n)
G = GL(2, F)
P.<x> = F[]
S = [P(t) for t in itertools.product(F, repeat=genus+2) if P(t)]

def action_by_degree(g, pol, d, x=x):
    m = g.matrix()
    num = m[0,0]*x + m[1,0]
    den = m[0,1]*x + m[1,1]
    return P(pol(num/den)*den^d)

# Compute action on binary forms.

ret1 = CayleyGroupRetract(G, S, lambda g, pol: action_by_degree(g, pol, genus+1))

V = VectorSpace(F2, (2*genus+3)*n)
def pol_to_vec(f):
    return [j for i in range(2*genus+3) for j in list(f[i])]
def vec_to_pol(v, n=n):
    return P([F([v[j+i].lift() for i in range(n)]) for j in range(0, (2*genus+3)*n, n)])

# Compute action on pairs.

pairs = {}
count = 0
for h in ret1.reps():
    G1 = ret1.stabilizer(h)
    G1order = G1.order()
    print(h, G1order)
    V1 = V.subspace([pol_to_vec((a^j*x^i)^2 + (a^j*x^i)*h) for i in range(genus+2) for j in range(n)])
    W = V.quotient(V1)
    
    def action(g, pol, W=W):
        pol1 = action_by_degree(g, pol, 2*(genus+1))
        vec1 = pol_to_vec(pol1)
        vec2 = W.lift(vec1)
        return vec_to_pol(vec2)
        
    S1 = [vec_to_pol(W.lift(w)) for w in W]
    S1 = [f for f in S1 if h.gcd(f.derivative()^2 - f*h.derivative()^2) == 1]
    if h.degree() < genus+1:
        S1 = [f for f in S1 if f[2*genus+1]^2 != f[2*genus+2]*h[genus]^2]
    ret2 = CayleyGroupRetract(G1, S1, action)
    pairs[h] = []
    for f in ret2.reps():
        order = ret2.stab_order(f) * 2
        count += 1/order
        pairs[h].append((f, order))

print("Total stacky count: {}".format(count))

Q.<T> = QQ[]
out = {}
for h in pairs:
    print(h)
    for (f, _) in pairs[h]:
#        lpoly = HyperellipticCurve(f,h).zeta_function().numerator()(T)
        lpoly = Q(list(magma.HyperellipticCurve(f,h).LPolynomial().Coefficients()))
        if lpoly not in out:
            out[lpoly] = []
        out[lpoly].append((f,h))
with open("genus_{}_hyp_over_F{}.txt".format(genus, 2**n), "w") as file:
    file.write(str(out))
