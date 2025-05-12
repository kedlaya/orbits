import random
from itertools import product, tee
from sage.misc.lazy_attribute import lazy_attribute
load("bfs.pyx")

def random_generating_sequence(G):
    """
    Construct a random sequence of generators of a finite group.
    
    This is likely to be quite short, and hence efficient for constructing Cayley graphs.
    
    EXAMPLES::
    
        sage: G = SymmetricGroup(10)
        sage: l = random_generating_sequence(G)
        sage: G.subgroup(l).order() # Should equal the order of G
        3628800
    """
    if not G.is_finite():
        return ValueError("Group must be finite")
    try:
        return [G(g) for g in G.gap().SmallGeneratingSet()]
    except AttributeError:
        l = []
        n = G.order()
        while G.subgroup(l).order() != n:
            l.append(G.random_element())
        return l

def binary_search_sort(n, i):
    """
    Sort ``range(n)`` according to a binary search for `i`.
    
    EXAMPLES::
    
        sage: [binary_search_sort(5, i) for i in range(5)]
        [[3, 4, 2, 1, 0],
        [3, 4, 2, 0, 1],
        [3, 4, 0, 1, 2],
        [0, 1, 2, 4, 3],
        [0, 1, 2, 3, 4]]
    """
    lower_limit = 0
    upper_limit = n
    if i < 0 or i >= n:
        raise ValueError("Must have 0 <= i < n")
    ans = []
    while lower_limit < i or upper_limit > i+1:
        middle = (lower_limit+upper_limit+1) // 2
        if i >= middle:
            ans.extend(range(lower_limit, middle))
            lower_limit = middle
        else:
            ans.extend(range(middle, upper_limit))
            upper_limit = middle
    ans.append(i)
    return ans

class CayleyGroupRetract():
    """
    Group retract object associated to a group action and a Cayley digraph.
    
    The underlying dict is stored as the attribute ``d``, but one can also index directly.
    For a vertex `v`, the value at `v` is a pair `(w,g)` where `w` is a connected component
    representative and `g` is a group element satisfying `g(w) = v`.

    If ``gens`` is specified, it is assumed to be a list of elements of `G`.
    These do not have to generate `G`; however, if they do not, then `order` is assumed
    to be the order of the subgroup that they generate.
    
    It is *not* required that `S` be closed under the action of `G`. To verify closure,
    set ``check_closure=True``.
    """
    def __init__(self, G, S, action, optimized_rep=None, check_closure=False, order=None, gens=None):
        self.G = G
        self._S = S # temporary
        self.action = action
        self.optimized_rep = optimized_rep if optimized_rep else (lambda g: g)
        self.identity = self.optimized_rep(G.one())
        self.gens = [self.optimized_rep(g) for g in random_generating_sequence(G)] if gens is None else gens
        self.seed = self.identity
        self.G_order = G.order() if order is None else order
        for _ in range(ceil(log(self.G_order, 2))):
            self.seed *= random.choice(self.gens)

        if check_closure:
            vertex_set = set(S)
            try:
                assert all(action(g, v) in vertex_set for g in self.gens for v in vertex_set)
            except AssertionError:
                raise AssertionError("Closure not verified")

    @lazy_attribute
    def d(self):
        # Conduct a depth-first search.
        iden = self.identity
        neighbors = lambda M, act=self.action, gens=self.gens: ((act(g, M), g) for g in gens)
        d = bfs(neighbors, self._S, self.identity)
        del self._S
        return d

    # Implement some dict functionality.

    def __getitem__(self, key):
        return self.d[key]

    def __iter__(self):
        return self.d.__iter__()

    def __contains__(self, item):
        return (item in self.d)
        
    def keys(self):
        return self.d.keys()

    def items(self):
        return self.d.items()

    def reps(self):
        """
        Return an iterator over connected component representatives.
        """
        for v, t in self.items():
            if t[0] == self.identity:
                yield v

    def rep(self, v):
        """
        Identify the chosen representative for the order containing a given element.
        """
        g0, _ = self[v]
        return (v if g0 == self.identity else self.action(~g0, v))

    def stab_order(self, v):
        """
        Compute the order of a point stabilizer.
        """
        # Force computation of the retract.
        _ = self.d

        # Use the orbit-stabilizer formula to compute the stabilizer order.
        _, orbit_len = self[self.rep(v)]
        return self.G_order // orbit_len

    def stabilizer(self, v, gap=False):
        """
        Compute a point stabilizer.
        
        Set ``gap=True`` to return a GAP group.
        """
        # Force computation of the retract.
        d = self.d

        # Use the orbit-stabilizer formula to compute the stabilizer order.
        g0, _ = self[v]
        mats0 = v if g0 == self.identity else self.action(~g0, v)
        _, orbit_len = self[mats0]

        # Early abort for the trivial orbit.
        gens = self.gens
        if orbit_len == 1:
            H = self.G.subgroup(gens, check=False)
            return H.gap() if gap else H

        # Early abort for the trivial group.
        if orbit_len == self.G_order:
            H = self.G.subgroup([])
            return H.gap() if gap else H

        H = self.G.subgroup([]).gap()
        g0inv = ~g0
        target_order = libgap(self.G_order // orbit_len)
        rgen = self.seed
        e1 = self.action(rgen, v)
        g1, _ = d[e1]
        while True:
            # Produce random stabilizer elements until we hit the right order.
            rgen *= random.choice(gens)
            g = rgen*g1
            e2 = self.action(rgen, e1)
            g2, _ = d[e2]
            h = g0*~g2*g*g0inv
            Gh = libgap(h)
            if Gh not in H: # Don't waste time if h is redundant
                H = H.ClosureGroupAddElm(Gh) # Subgroup of G generated by H and h
                if H.Size() == target_order:
                    self.seed = rgen
                    return H if gap else G.subgroup(H.SmallGeneratingSet())
            e1, g1 = e2, g2

class OrbitLookupTree():
    r"""
    Class for orbit lookup trees.
    
    The internal tree is stored as ``self.tree``, but one can also index directly into ``self``.
    Each level ``self[k]`` is a dictionary keyed by a `k`-tuple, identified with nodes of the tree.
    Each value ``self[k][U]`` is a dictionary with the following keys:
    - ``gpel``: a dict of the form `z: (U', g)` where `g(U') = U \cup \{z\}`.
    - ``stab``: the stabilizer of `U`.
    - ``retract`` (for nontrivial stabilizer): a dictionary whose value at `y \in S \setminus U` is an element `g \in G_U` such that `U \cup \{g^{-1}(y)\}` is an orbit representative for `G_U`.    
    """

    def __init__(self, G, vertices, methods=None, check_closure=True):
        r"""
        The entries of ``methods`` (all optional):
 
        - ``action``: on input of a group element `g` and a vertex `x`, returns 
          the action of `g` on `x`. Defaults to ``g*x``.
        - ``optimized_rep``: converts an element of `G` into a representation expected 
          by ``action``.
        - ``forbid``: on input of a tuple, returns ``True`` if the underlying set should 
          be forbidden. This is assumed to be both invariant under both the `G`-action and
          permutation of the tuple, but not necessarily under passage to a superset.
        """
        self.G = G
        self.G_order = G.order()
        self.V = vertices
        self.initialize_vertices()
        
        if methods is None:
            methods = {}
        self.action = methods['action'] if 'action' in methods else (lambda g, x: g*x)
        self.optimized_rep = methods['optimized_rep'] if 'optimized_rep' in methods else (lambda g: g)
        self.forbid = methods['forbid'] if 'forbid' in methods else None
        self.identity = self.optimized_rep(G.one())
        self.depth = 0

        self.G_gens = [self.optimized_rep(g) for g in random_generating_sequence(G)]
        if check_closure:
            for g in self.G_gens:
                assert all(self.action(g, x) in self.S for x in self.S)
        self.tree = {'data': {'stab': (self.G_order, self.G_gens)}}
        
    def initialize_vertices(self):
        """
        Create a canonical copy of the action set.
        
        This eliminates the creation in memory of many copies of the same elements.
        """
        self.S = dict(zip(self.V, self.V))   

    def __getitem__(self, key):
        if self.depth < len(key):
            raise ValueError("Tree not computed to depth {}".format(len(key)))
        d = self.tree
        for i in key:
            d = d[i]
        return d

    def orbit_reps(self, n, with_tree=False):
        r"""
        Return an iterator over orbit representatives at depth `n`.
        """
        if self.depth < n:
            raise ValueError("Tree not computed to depth {}".format(n))
        if n == 0:
            yield ((), self.tree) if with_tree else ()
        else:
            queue = [iter(self.tree.items())]
            vals = []
            while True:
                try:
                    v, w = next(queue[-1])
                    if v != "data":
                        vals.append(v)
                        if len(vals) == n:
                            yield (tuple(vals), w) if with_tree else tuple(vals)
                            vals.pop()
                        else:
                            queue.append(iter(w.items()))
                except StopIteration:
                    queue.pop()
                    try:
                        vals.pop()
                    except IndexError:
                        break

    def count_orbit_reps(self, n):
        r"""
        Return the number of orbit representatives at depth `n`.
        """
        return sum(1 for _ in self.orbit_reps(n))

    def residual_vertices(self, mats, sub=None):
        """
        Return a generator for the action set for the residual action associated to a node.
        """
        return (M for M in self.V if M not in mats)

    def lift(self, x, data):
        """
        Return a representative of the quotient relative to a particular node.
        """
        return x

    def _orbit_rep(self, l, n, find_node=True):
        """
        Find orbit representatives for a list of tuples.

        This is structured for internal use. Use ``orbit_rep`` instead.
        """
        if n == 0:
            return {(): ((), self.identity)}
        # Prepare truncations for recursive classification.
        l = tuple(l)
        truncations = set(mats[:-1] for mats in l)
        # Run the recursion and file the results.
        cache = self._orbit_rep(truncations, n-1)
        # Finish with retracts.
        ans = {}
        for mats in l:
            mats0, g0 = cache[mats[:-1]]
            if mats0 is None: # Found an ineligible tuple
                ans[mats] = (None, None)
                continue
            parent = self[mats0]['data']
            y = self.lift(self.action(~g0, mats[-1]), parent)
            if parent['stab'][0] == 1: # Trivial stabilizer, no retract stored
                g1 = self.identity
            else:
                g1, _ = parent['retract'][y]
            z = y if g1 == self.identity else self.lift(self.action(~g1, y), parent)
            if not find_node: # Abridged operation
                mats1 = mats0 + (z,)
                ans[mats] = (mats1, g0*g1)
            else:
                try:
                    mats2, g2 = parent['gpel'][z]
                    ans[mats] = (mats2, g0*g1*g2)
                except KeyError: # Found an ineligible tuple
                    ans[mats] = (None, None)
        return ans
    
    def orbit_rep_lookup(self, mats):
        """
        Find the orbit representative for a given tuple.
        
        The output consists of a pair ``(mats1, g)`` such that the action of `g` on `mats` gives `mats`.
        """
        n = len(mats)
        if n not in self:
            raise ValueError("Tree not computed to depth {}".format(n))
        return self._orbit_rep([mats], n)[mats]

    def stabilizer(self, mats, sub=None):
        """
        Compute the stabilizer of a subset of vertices.
        
        Outputs the order of the group and a short generating sequence.
        """
        selfnmats = (sub if sub else self[mats])['data']
        if selfnmats['stab'][0] > 0: # Already computed
            return selfnmats['stab']
        parent = self[mats[:-1]]['data']
        if parent['stab'][0] == 1: # Parent has trivial stabilizer
            G1_gap = self.G.subgroup([]).gap()
        else:
            G1_gap = parent['retract'].stabilizer(mats[-1], gap=True)
        G2_gap = G1_gap.ClosureGroup([libgap(g) for g in selfnmats['stab'][1]])
        order = G2_gap.Size().sage()
        G = self.G
        gens = [self.optimized_rep(G(g)) for g in G2_gap.SmallGeneratingSet()]
        selfnmats['stab'] = (order, gens)
        return selfnmats['stab']

    def construct_retract(self, mats, sub):
        """
        Construct the Cayley group retract attached to a node.
        """
        order, gens = self.stabilizer(mats, sub)
        S = self.S
        vertices = (S[M] for M in self.residual_vertices(mats, sub))

        if order == 1:
            sub['data']['gpel'] = dict.fromkeys(vertices)
        else:
            action = lambda g, x, act=self.action, lift=self.lift, data=sub['data']: lift(act(g, x), data)
            retract = CayleyGroupRetract(self.G, vertices, action, self.optimized_rep, gens=gens, order=order)
            sub['data']['retract'] = retract
            sub['data']['gpel'] = dict.fromkeys(retract.reps())

    def predicted_count(self, n):
        """
        Compute the size of the implicit target of the action at depth `n`.
        """
        return binomial(len(self.V), n)

    def retracts_at_new_level(self, verbose=False):
        """
        Compute retracts at the bottom level of the tree.
        """
        n = self.depth
        if verbose:
            print("Original depth: {}".format(n))
        check_count = 0
        node_count = 0
        for (mats, sub) in self.orbit_reps(n, with_tree=True):
            order, _ = self.stabilizer(mats, sub)
            if not self.forbid:
                assert self.G_order % order == 0
                check_count += self.G_order // order
            self.construct_retract(mats, sub)
            if verbose:
                node_count += 1
                print("Computed a retract with stabilizer order {} (count: {})".format(order, node_count))
        # If no forbidden vertices, check the orbit-stabilizer formula.
        if not self.forbid and check_count != self.predicted_count(n):
            raise RuntimeError("Error in orbit-stabilizer formula")
        if verbose:
            count = sum(len(sub['data']['gpel']) for _, sub in self.orbit_reps(n, with_tree=True))
            print("Number of nodes in retracts: {}".format(count))

    def apply_transporter(self, M, mats):
        return tuple(mats[i] for i in M)

    def transporters(self, n):
        return [binary_search_sort(n, j) for j in range(n-1)]

    def create_new_nodes(self, verbose=False):
        """
        Create nodes at a new level of the tree.
        """
        n = self.depth
        self.depth = n+1
        transporters = self.transporters(n+1)
        for mats0, sub in self.orbit_reps(n, with_tree=True):
            for z, _ in sub['data']['gpel'].items():
                if _ is not None: # Already encountered this node
                    continue
                mats = mats0 + (z,)
                tmp = [self.apply_transporter(t, mats) for t in transporters]
                tmp2 = self._orbit_rep(tmp, n+1, find_node=False).values()
                if self.forbid and (any(i[0] is None for i in tmp2) or self.forbid(mats)):
                    sub['data']['gpel'][z] = ()
                    for (mats1, _) in tmp2:
                        if mats1 is not None:
                            self[mats1[:-1]]['data']['gpel'][mats1[-1]] = ()
                else:
                    l = []
                    sub[z] = {'data': {'stab': (0, l)}} # New node
                    sub['data']['gpel'][z] = (mats, self.identity)
                    for mats1, g1 in tmp2:
                        if mats1 == mats:
                            l.append(g1) # Stabilizer element
                        else:
                            self[mats1[:-1]]['data']['gpel'][mats1[-1]] = (mats, ~g1)
            if self.forbid: # Remove forbidden elements
                sub['data']['gpel'] = {z: g for z, g in sub['data']['gpel'].items() if g != ()}
        if verbose:
            print("Number of new nodes: {}".format(self.count_orbit_reps(n+1)))
            print("New level: {}".format(n+1))
            print()

    def extend(self, n, verbose=False):
        r"""
        Extend the tree to a new depth.
        """
        while self.depth < n:
            libgap.collect()
            self.retracts_at_new_level(verbose)
            self.create_new_nodes(verbose)

class LinearOrbitLookupTree(OrbitLookupTree):
    r"""
    Class for linear orbit lookup trees.
    """
    def initialize_vertices(self):
        S = (as_immutable(v) for v in self.V if first_nonzero(v) == 1)
        self.S = dict(zip(*tee(S, 2)))
        self.full = (self.V.ambient_vector_space() is self.V)
        if self.full:
            self.coords = lambda x: x
        else:
            self.coords = lambda x, V=self.V: V.coordinate_vector(x)
        self.V_basis = self.V.basis()
        self.F = self.V.base_field()
        self.q = self.F.cardinality()

    def residual_vertices(self, mats, sub=None):
        quot = self.V.quotient(self.V.subspace(mats))
        section_on_basis = tuple(as_immutable(quot.lift(quot(v))) for v in self.V_basis)
        if sub is None:
            sub = self[mats]
        if self.full:
            sub['data']['section_on_basis'] = Matrix(section_on_basis).transpose()
        else:
            sub['data']['section_on_basis'] = section_on_basis
        lifts = [quot.lift(v) for v in quot.basis()]
        d = quot.dimension()
        return (as_immutable(sumprod(t, lifts)) for t in product(self.F, repeat=d) if first_nonzero(t) == 1)

    def normalize(self, x):
        ans = x if self.q == 2 else x / first_nonzero(x)
        return as_immutable(ans)

    def lift(self, x, data):
        if self.full:
            return self.normalize(data['section_on_basis']*x)
        return self.normalize(sumprod(self.coords(x), data['section_on_basis']))

    def predicted_count(self, n):
        dim = self.V.dimension()
        F = self.V.base_field()
        q = F.cardinality()
        return prod(q**(dim-i)-1 for i in range(n)) // prod(q**(n-i)-1 for i in range(n))

    def apply_transporter(self, M, mats):
        return tuple(self.normalize(sumprod(i, mats)) for i in M.rows())

    def transporters(self, n):
        cache = []
        F = self.V.base_field()
        W = VectorSpace(F, n)
        for w in W:
            if not w[:n-1]:
                continue
            vecs = []
            for v in W:
                if v.dot_product(w) == 0 and Matrix(vecs + [v]).rank() > len(vecs):
                    vecs.append(v)
                    if len(vecs) == n-1:
                        break
            quot = W.quotient(W.subspace(vecs))
            vecs.append(quot.lift(quot.basis()[0]))
            cache.append(Matrix(vecs))
        return cache

