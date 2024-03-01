import random
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
        return G.gap().SmallGeneratingSet()
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
        self.action = action
        self.optimized_rep = optimized_rep if optimized_rep else (lambda g: g)
        self.gens = [self.optimized_rep(g) for g in random_generating_sequence(G)] if gens is None else gens
        self.G_order = G.order() if order is None else order

        if check_closure:
            vertex_set = set(S)
            assert all(action(g, v) in vertex_set for g in self.gens for v in vertex_set)

        # Conduct a breadth-first search.
        d = {}
        iden = self.optimized_rep(G(1))
        neighbors = lambda M, action=self.action, gens=self.gens: ((action(g, M), g) for g in gens)
        for v in S:
            if v not in d:
                d[v] = (v, iden, 0)
                orbit_len = dfs(neighbors, d, v)
        # Avoid using fresh copies of elements of S.
        self.d = {v: d[v] for v in S}
        self.d.update({v: d[v] for v in d if v not in self.d})

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
            if t[0] == v:
                yield v

    def stabilizer(self, v, gap=False):
        """
        Compute a point stabilizer.
        
        Set ``gap=True`` to return a GAP group.
        """
        # Use the orbit-stabilizer formula to compute the stabilizer order.
        G = self.G
        mats0, g0, _ = self[v]
        orbit_len = self[mats0][2]
        target_order = ZZ(self.G_order / orbit_len)

        # Early abort for the trivial orbit.
        if orbit_len == 1:
            H = G.subgroup(self.gens)
            return H.gap() if gap else H

        # Early abort for the trivial group.
        if target_order == 1:
            H = G.subgroup([])
            return H.gap() if gap else H

        d = self.d
        orbit = [w for w in d if d[w][0] == mats0]
        order = 1
        H = G.subgroup([]).gap()
        while order < target_order:
            # Produce random stabilizer elements until we hit the right order.
            e1 = random.choice(orbit)
            mats1, g1, _ = d[e1]
            assert mats1 == mats0
            rgen = random.choice(self.gens)
            e2 = self.action(rgen, e1)
            mats2, g2, _ = d[e2]
            assert mats2 == mats0
            g = rgen*g1
            if g == g2: # Don't bother with the identity element
                continue
            h = g0*~g2*g*~g0
            Gh = G(h)
            if Gh not in H:
                H = H.ClosureGroup(Gh) # Subgroup of G generated by H and h
                order = H.Size().sage()
        return H if gap else G.subgroup(H.SmallGeneratingSet())

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

    def __init__(self, G, vertices, methods=None):
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
        self.S = {v: v for v in self.V} # Use this to find canonical copies in memory
        
        if methods is None:
            methods = {}
        self.action = methods['action'] if 'action' in methods else (lambda g, x: g*x)
        self.optimized_rep = methods['optimized_rep'] if 'optimized_rep' in methods else (lambda g: g)
        self.forbid = methods['forbid'] if 'forbid' in methods else None
        self.identity = self.optimized_rep(G(1))
        self.depth = 0

        self.G_gens = [self.optimized_rep(g) for g in random_generating_sequence(G)]
        for g in self.G_gens:
            assert all(self.action(g, x) in vertices for x in vertices)
        self.tree = {'data': {'stab': (self.G_order, self.G_gens)}}

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
            while queue:
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
                    if queue:
                        vals.pop()

    def count_orbit_reps(self, n):
        r"""
        Return the number of orbit representatives at depth `n`.
        """
        return sum(1 for _ in self.orbit_reps(n))

    def canonicalize(self, x):
        return self.S[x]

    def residual_action(self, mats, sub=None):
        """
        Compute the residual action associated to a node.
        """
        vertices = [M for M in self.V if M not in mats]
        action = self.action
        if sub is None:
            sub = self[mats]
        sub['data']['quot'] = self.canonicalize
        return vertices, action

    def _orbit_rep(self, l, n, find_node=True):
        """
        Find orbit representatives for a list of tuples.

        This is structured for internal use. Use ``orbit_rep`` instead.
        """
        if n == 0:
            return [(mats, self.identity) for mats in l]
        # Prepare truncations for recursive classification.
        l = list(l)
        cache = list(set(mats[:-1] for mats in l))
        # Run the recursion and file the results.
        cache = dict(zip(cache, self._orbit_rep(cache, n-1)))
        # Finish with retracts.
        ans = []
        for mats in l:
            mats0, g0 = cache[mats[:-1]]
            if mats0 is None: # Found an ineligible tuple
                ans.append((None, None))
                continue
            parent = self[mats0]['data']
            y = self.action(~g0, mats[-1])
            y = parent['quot'](y) # Canonicalize representative
            if parent['stab'][0] == 1: # Trivial stabilizer, no retract needed
                z = y
                g1 = self.identity
            else:
                z, g1, _ = parent['retract'][y]
            if not find_node: # Abridged operation
                mats1 = mats0 + (z,)
                ans.append((mats1, g0*g1))
            elif z not in parent['gpel']: # Found an ineligible tuple
                ans.append((None, None))
            else:
                mats2, g2 = parent['gpel'][z]
                ans.append((mats2, g0*g1*g2))
        return ans
    
    def orbit_rep_lookup(self, mats):
        """
        Find the orbit representative for a given tuple.
        
        The output consists of a pair ``(mats1, g)`` such that the action of `g` on `mats` gives `mats`.
        """
        n = len(mats)
        if n not in self:
            raise ValueError("Tree not computed to depth {}".format(n))
        return self._orbit_rep([mats], n)[0]

    def stabilizer(self, mats, sub=None):
        """
        Compute the stabilizer of a subset of vertices.
        
        Outputs the order of the group and a short generating sequence.
        """
        n = len(mats)
        selfnmats = (sub if sub else self[mats])['data']
        if selfnmats['stab'][0] > 0: # Already computed
            return selfnmats['stab']
        parent = self[mats[:-1]]['data']
        if parent['stab'][0] == 1: # Parent has trivial stabilizer
            G1_gap = G.subgroup([]).gap()
        else:
            G1_gap = parent['retract'].stabilizer(mats[-1], gap=True)
        G2_gap = G1_gap.ClosureGroup(selfnmats['stab'][1])
        order = G2_gap.Size().sage()
        optimized_gens = [self.optimized_rep(g) for g in G2_gap.SmallGeneratingSet()]
        selfnmats['stab'] = (order, optimized_gens)
        return selfnmats['stab']

    def construct_retract(self, mats, sub):
        """
        Construct the Cayley group retract attached to a node.
        """
        order, gens = self.stabilizer(mats, sub)
        vertices, action = self.residual_action(mats, sub)
        if order > 1:
            retract = CayleyGroupRetract(self.G, vertices, action, self.optimized_rep, gens=gens, order=order)
            sub['data']['retract'] = retract
        sub['data']['gpel'] = {M: None for M in (vertices if order == 1 else retract.reps())}

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
        return tuple(mats[M[i]] for i in range(len(mats)))

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
                tmp2 = self._orbit_rep(tmp, n+1, find_node=False)
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
            print("Number of new nodes: {}".format(sum(1 for _ in self.orbit_reps(n+1))))
            print("New level: {}".format(n+1))
            print()

    def extend(self, n, verbose=False):
        r"""
        Extend the tree to a new depth.
        """
        while self.depth < n:
            self.retracts_at_new_level(verbose)
            self.create_new_nodes(verbose)

class LinearOrbitLookupTree(OrbitLookupTree):
    r"""
    Class for linear orbit lookup trees.
    """
    def residual_action(self, mats, sub=None):
        quot = self.V.quotient(self.V.subspace(mats))
        lifts = [quot.lift(v) for v in quot.basis()]
        W = VectorSpace(GF(2), quot.dimension())

        # Generate elements of the quotient space represented by canonical elements of V.
        vertices = [self.S[as_immutable(sum(i*j for i,j in zip(lifts, W.coordinates(w))))] for w in W if w]
        section_on_basis = [quot.lift(quot(v)) for v in self.V.basis()]
        def section(x, section_on_basis=section_on_basis, V=self.V, S=self.S):
            y = V(0)
            for a,b in zip(V.coordinates(x), section_on_basis):
                y += a*b
            return S[as_immutable(y)]
        if sub is None:
            sub = self[mats]
        sub['data']['quot'] = section
        action = lambda g, x, section=section, action=self.action: section(action(g, x))
        return vertices, action

    def predicted_count(self, n):
        dim = self.V.dimension()
        return prod(2**(dim-i)-1 for i in range(n)) // prod(2**(n-i)-1 for i in range(n))

    def apply_transporter(self, M, mats):
        n = len(mats)
        return tuple(self.S[as_immutable(sum(M[i,j]*mats[j] for j in range(n)))] for i in range(n))

    def transporters(self, n):
        cache = []
        W = VectorSpace(GF(2), n)
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


