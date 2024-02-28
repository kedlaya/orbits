import random
load("bfs.pyx")

def return_immutable(v):
    """
    Return v after having made it immutable.
    
    This is useful for generating an immutable vector in an expression (e.g., in a lambda function).
    """
    v.set_immutable()
    return v

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
    representative and `g` is a group element satisfying `g(w) = v`. Any vertex sharing a
    component in a vertex in `exclude`, or for which `forbid` (if specified) returns `True`,
    is omitted.

    If ``gens`` is specified, it is assumed to be a list of elements of `G`.
    These do not have to generate `G`; however, if they do not, then `order` is assumed
    to be the order of the subgroup that they generate.
    
    It is *not* required that `S` be closed under the action of `G`. To verify closure,
    set ``check_closure=True``.
    """
    def __init__(self, G, S, action, optimized_rep=None, check_closure=False, order=None, gens=None):
        self.G = G
        self.vertices = list(S)
        self.action = action
        self.optimized_rep = optimized_rep if optimized_rep else (lambda g: g)
        self.gens = [self.optimized_rep(g) for g in random_generating_sequence(G)] if gens is None else gens
        if check_closure:
            vertex_set = set(S)
            assert all(action(g, v) in vertex_set for g in self.gens for v in vertex_set)
        self.G_order = G.order() if order is None else order

        # Conduct a breadth-first search.
        d = {}
        iden = self.optimized_rep(G(1))
        self.orbit_len = {}
        neighbors = lambda M, action=self.action, gens=self.gens: ((action(g, M), g) for g in gens)
        for v in self.vertices:
            if v not in d:
                d[v] = (v, iden, 0)
                orbit_len = dfs(neighbors, d, v)
                d[v] = (v, iden, orbit_len)
        self.d = d

    def __getitem__(self, key):
        return self.d[key]

    def __iter__(self):
        return self.d.__iter__()

    def __contains__(self, item):
        return (item in self.d)
        
    def items(self):
        return self.d.items()

    def keys(self):
        return self.d.keys()

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
        mats0, g0, _ = self[v]

        # Use the orbit-stabilizer formula to compute the stabilizer order.
        orbit_len = self[mats0][2]
        target_order = ZZ(self.G_order / orbit_len)
        H = G.subgroup([]).gap()

        # Early abort for the trivial group.
        if target_order == 1:
            return H if gap else G.subgroup([])

        d = self.d
        orbit = [w for w in self.vertices if d[w][0] == mats0]
        order = 1
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
            Gh = self.G(h)
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
    - ``gpel`` (for `U` eligible): a pair `(U', g)` such that `U'` is a green node and `g(U') = U`.
    - ``stab`` (for `U` green): the stabilizer of `U`.
    - ``retract`` (for `U` green and `k<n`): a dictionary whose value at `y \in S \setminus U` (resp. `y \in S/U`) is an element `g \in G_U` such that `U \cup \{g^{-1}(y)\}` (resp. `\pi_U^{-1}(g^{-1}(y))`) is a red or green node.    
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
        
        if methods is None:
            methods = {}
        self.action = methods['action'] if 'action' in methods else methods['apply_group_elem'] if 'apply_group_elem' in methods else (lambda g, x: g*x)
        self.optimized_rep = methods['optimized_rep'] if 'optimized_rep' in methods else (lambda g: g)
        self.forbid = methods['forbid'] if 'forbid' in methods else None
        self.identity = self.optimized_rep(G(1))
        S0 = tuple()
        self.tree = {0: {S0: {'gpel': (S0, self.identity), 'stab': (0, [])}}}

        try:
            S = set(vertices)
        except TypeError:
            S = vertices
        self.G_gens = [self.optimized_rep(g) for g in random_generating_sequence(G)]
        for g in self.G_gens:
            assert all(self.action(g, x) in S for x in S)

    def __getitem__(self, key):
        return self.tree[key]

    def __contains__(self, item):
        return (item in self.tree)

    def depth(self):
        """
        Compute the current depth of the tree.
        """
        return max(self.tree.keys())

    def residual_action(self, mats):
        n = len(mats)
        vertices = [M for M in self.V if M not in mats]
        action = self.action
        self[n][mats]['quot'] = lambda x: x    
        return vertices, action

    def green_nodes(self, n):
        r"""
        Return an iterator over green nodes (orbit representatives) at depth `n`.
        """
        for mats, selfnmats in self[n].items():
            if 'stab' in selfnmats:
                yield mats

    def _orbit_rep(self, l, n, find_green=True):
        """
        Find orbit representatives for a list of tuples.

        This is structured for internal use. Use ``orbit_rep`` instead.
        """
        if n == 0:
            return [(mats, self.identity) for mats in l]
        ans = []
        # Prepare truncations for recursive classification.
        l = list(l)
        l0 = [mats[:-1] for mats in l]
        cache = {}
        for mats0 in l0:
            if mats0 not in cache:
                if mats0 in self[n-1] and 'stab' in self[n-1][mats0]: # Truncation is green
                    cache[mats0] = (mats0, self.identity)
                else: # Truncation needs to be resolved
                    cache[mats0] = () # Record a dummy value to eliminate duplication in queue
        # Run the recursion and file the results.
        if cache:
            cache.update(zip(cache.keys(), self._orbit_rep(cache.keys(), n-1)))
        # Finish with retracts.
        ans = []
        for mats in l:
            mats0, g0 = cache[mats[:-1]]
            if mats0 is None: # Found an ineligible node
                ans.append((None, None))
                continue
            y = mats[-1] if g0 == self.identity else self.action(~g0, mats[-1])
            y = self[n-1][mats0]['quot'](y) # Canonicalize representative
            if self[n-1][mats0]['stab'][0] == 1: # Trivial stabilizer, no retract needed
                z = y
                g1 = self.identity
            else:
                z, g1, _ = self[n-1][mats0]['retract'][y]
            mats1 = mats0 + (z,)
            if not find_green: # Abridged operation
                ans.append((mats1, g0*g1))
            elif mats1 not in self[n]: # Found an ineligible node
                ans.append((None, None))
            else:
                mats2, g2 = self[n][mats1]['gpel']
                ans.append((mats2, g0*g1*g2))
        return ans
    
    def orbit_rep(self, mats):
        """
        Find the orbit representative for a given tuple.
        
        The output consists of a pair ``(mats1, g)`` such that the action of `g` on `mats` gives `mats`.
        """
        n = len(mats)
        if n not in self:
            raise ValueError("Tree not computed to depth {}".format(n))
        return self._orbit_rep([mats], n)[0]

    def stabilizer(self, mats):
        """
        Compute the stabilizer of a subset of vertices.
        
        Outputs the order of the group and a short generating sequence.
        """
        n = len(mats)
        selfnmats = self[n][mats]
        if selfnmats['stab'][0] > 0: # Already computed
            return selfnmats['stab']
        if n == 0:
            selfnmats['stab'] = (self.G_order, self.G_gens)
            return selfnmats['stab']
        parent = mats[:-1]
        if self[n-1][parent]['stab'][0] == 1: # Parent has trivial stabilizer
            G1_gap = G.subgroup([]).gap()
        else:
            retract = self[n-1][parent]['retract']
            G1_gap = retract.stabilizer(mats[-1], gap=True)
        G2_gap = G1_gap.ClosureGroup(selfnmats['stab'][1])
        order = G2_gap.Size().sage()
        optimized_gens = [self.optimized_rep(g) for g in G2_gap.SmallGeneratingSet()]
        selfnmats['stab'] = (order, optimized_gens)
        return selfnmats['stab']

    def construct_children(self, mats):
        """
        Construct the children of a green node using a Cayley group retract.
        """
        n = len(mats)
        order, gens = self.stabilizer(mats)
        vertices, action = self.residual_action(mats)
        if order > 1:
            retract = CayleyGroupRetract(self.G, vertices, action, self.optimized_rep, gens=gens, order=order)
            self[n][mats]['retract'] = retract
        for M in (vertices if order == 1 else retract.reps()):
            if M in mats:
                raise ValueError("Found repeated entry in tuple")
            mats1 = mats + (M,)
            self[n+1][mats1] = {}

    def predicted_count(self, n):
        return binomial(len(self.V), n)

    def nodes_at_new_level(self, verbose=False):
        """
        Compute nodes at a new level of the tree (without classifying them).
        """
        n = self.depth()
        if verbose:
            print("Original depth: {}".format(n))
        self.tree[n+1] = {}
        check_count = 0
        for mats in self.green_nodes(n):
            order, _ = self.stabilizer(mats)
            if not self.forbid:
                assert self.G_order % order == 0
                check_count += self.G_order // order
            self.construct_children(mats)
            if verbose:
                print("Constructed children of a node with stabilizer order {}".format(order))
        # If no forbidden vertices, check the orbit-stabilizer formula.
        if not self.forbid:
            if check_count != self.predicted_count(n):
                raise RuntimeError("Error in orbit-stabilizer formula")
        if verbose:
            print("Number of new nodes: {}".format(len(self[n+1])))

    def apply_transporter(self, M, mats):
        return tuple(mats[M[i]] for i in range(len(mats)))

    def transporters(self, n):
        return [(lambda mats, M=binary_search_sort(n, j): self.apply_transporter(M, mats)) for j in range(n-1)]

    def classify_nodes(self, verbose=False):
        """
        Classify nodes at the last level of the tree.
        """
        n = self.depth()
        selfn = self[n]
        transporters = self.transporters(n)
        for mats in selfn:
            if 'gpel' in selfn[mats]: # Already encountered this node
                continue
            tmp = [t(mats) for t in transporters]
            tmp2 = self._orbit_rep(tmp, n, find_green=False)
            if self.forbid and (any(i[0] is None for i in tmp2) or self.forbid(mats)):
                selfn[mats]['gpel'] = None
                for (mats1, _) in tmp2:
                    if mats1 is not None:
                        selfn[mats1]['gpel'] = None
            else:
                selfn[mats]['gpel'] = (mats, self.identity)
                selfn[mats]['stab'] = (0, [])
                for mats1, g1 in tmp2:
                    if mats1 == mats:
                        selfn[mats]['stab'][1].append(g1) # Stabilizer element
                    else:
                        selfn[mats1]['gpel'] = (mats, ~g1)
        if self.forbid: # Remove black nodes
            nodes_to_delete = [mats for mats in selfn if selfn[mats]['gpel'] is None]
            for mats in nodes_to_delete:
                del selfn[mats]
        if verbose:
            print("Number of new green nodes: {}".format(sum(1 for _ in self.green_nodes(n))))
            print("New level: {}".format(n))
            print()

    def extend(self, n, verbose=False):
        r"""
        Extend the tree to a new depth.
        """
        while self.depth() < n:
            self.nodes_at_new_level(verbose)
            self.classify_nodes(verbose)

class LinearOrbitLookupTree(OrbitLookupTree):
    r"""
    Class for linear orbit lookup trees.
    """
    def residual_action(self, mats):
        quot = self.V.quotient(self.V.subspace(mats))
        lifts = [quot.lift(v) for v in quot.basis()]
        W = VectorSpace(GF(2), quot.dimension())
        vertices = [sum(i*j for i,j in zip(lifts, W.coordinates(w))) for w in W if w]
        for v in vertices:
            v.set_immutable()
        section_on_basis = [quot.lift(quot(v)) for v in self.V.basis()]
        def section(x, section_on_basis=section_on_basis, V=self.V):
            y = V(0)
            for a,b in zip(V.coordinates(x), section_on_basis):
                y += a*b
            y.set_immutable()
            return y       
        self[len(mats)][mats]['quot'] = section
        action = lambda g, x, section=section, action=self.action: section(action(g, x))
        return vertices, action

    def predicted_count(self, n):
        dim = self.V.dimension()
        return prod(2**(dim-i)-1 for i in range(n)) // prod(2**(n-i)-1 for i in range(n))

    def apply_transporter(self, M, mats):
        n = len(mats)
        mats1 = tuple(sum(M[i,j]*mats[j] for j in range(n)) for i in range(n))
        for i in mats1:
            i.set_immutable()
        return mats1

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
            cache.append(lambda mats, M=Matrix(vecs): self.apply_transporter(M, mats))
        return cache


