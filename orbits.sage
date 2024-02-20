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

class GroupAction():
    """
    Action of a finite group on a finite set.
    """
    def __init__(self, G, vertices):
        self.G = G
        self.vertices = vertices
        # Check closure under the action.
        S = set(self.vertices)
        self.G_gens = [self.optimized_rep(g) for g in random_generating_sequence(G)]
        for g in self.G_gens:
            assert all(self.action(g, x) in S for x in S)
        
    def action(self, g, v):
        return g*v
        
    def optimized_rep(self, g):
        return g

class GroupRetract():
    """
    Group retract object associated to a group action and a partial Cayley digraph.
    
    The underlying dict is stored as the attribute ``d``, but one can also index directly.
    For a vertex `v`, the value at `v` is a pair `(w,g)` where `w` is a connected component
    representative and `g` is a group element satisfying `g(w) = v`. Any vertex sharing a
    component in a vertex in `exclude`, or for which `forbid` (if specified) returns `True`,
    is omitted.

    The argument ``neighbors`` should be a dict whose value at `v` is a list of pairs
    consisting of out-neighbors of `v` and edge labels. For efficiency, we assume that every
    connected component of the digraph is strongly connected; otherwise, the reverse edges
    should also be included.
    """
    def __init__(self, G, vertices, neighbors, exclude=[], forbid=None, optimized_rep=None):
        self.G = G
        vertices = list(vertices)
        self.optimized_rep = optimized_rep if optimized_rep else (lambda g: g)
        # Conduct a breadth-first search, identifying forbidden vertices.
        d = {}
        iden = self.optimized_rep(G(1))
        forbidden_reps = set()
        self.orbit_len = {}
        for v in vertices:
            if v not in d:
                if forbid and forbid(v):
                    forbidden_reps.add(v)
                d[v] = (v, iden)
                self.orbit_len[v] = dfs(neighbors, d, v)
        # Identify orbit representatives of excluded vertices.
        forbidden_reps.update(d[v][0] for v in exclude)
        # Remove forbidden and excluded orbits.
        self.d = {v: d[v] for v in d if d[v][0] not in forbidden_reps} if forbidden_reps else d

    def __getitem__(self, key):
        return self.d[key]

    def __iter__(self):
        return self.d.__iter__()

    def __contains__(self, item):
        return (item in self.d)

    def items(self):
        return self.d.items()

    def vertices(self):
        return self.d.keys()

    def reps(self):
        """
        Return an iterator over connected component representatives.
        """
        for v, t in self.items():
            if t[0] == v:
                yield v

class CayleyGroupRetract(GroupRetract):
    """
    Specialized version of GroupRetract for full Cayley digraphs.

    If ``gens`` is specified, it is assumed to be a list of elements of `G`.
    These do not have to generate `G`; however, if they do not, then `order` is assumed
    to be the order of the subgroup that they generate.
    """
    def __init__(self, G, vertices, action, optimized_rep=None, debug=False, order=None, gens=None):
        self.action = action
        self.optimized_rep = optimized_rep if optimized_rep else (lambda g: g)
        self.gens = [self.optimized_rep(g) for g in random_generating_sequence(G)] if gens is None else gens
        if debug:
            vertex_set = set(vertices)
            assert all(action(g, v) in vertex_set for g in self.gens for v in vertex_set)
        neighbors = lambda M, action=action, gens=self.gens: ((action(g, M), g) for g in gens)
        self.G_order = G.order() if order is None else order
        GroupRetract.__init__(self, G, vertices, neighbors, optimized_rep=optimized_rep)

    def stabilizer(self, v, gap=False):
        """
        Compute a point stabilizer.
        
        Set ``gap=True`` to return a GAP group.
        """
        mats0, g0 = self[v]

        # Use the orbit-stabilizer formula to compute the stabilizer order.
        target_order = ZZ(self.G_order / self.orbit_len[mats0])
        H = G.subgroup([]).gap()

        # Early abort for the trivial group.
        if target_order == 1:
            return H if gap else G.subgroup([])

        d = self.d
        orbit = [w for w in self.vertices() if d[w][0] == mats0]
        order = 1
        while order < target_order:
            # Produce random stabilizer elements until we hit the right order.
            e1 = random.choice(orbit)
            mats1, g1 = d[e1]
            assert mats1 == mats0
            rgen = random.choice(self.gens)
            e2 = self.action(rgen, e1)
            mats2, g2 = d[e2]
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

    def __init__(self, G, vertices, methods=None, linear=False):
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
        self.vertices = vertices
    
        if methods is None:
            methods = {}
        self.action = methods['action'] if 'action' in methods else methods['apply_group_elem'] if 'apply_group_elem' in methods else (lambda g, x: g*x)
        self.optimized_rep = methods['optimized_rep'] if 'optimized_rep' in methods else (lambda g: g)
        self.forbid = methods['forbid'] if 'forbid' in methods else None
        self.identity = self.optimized_rep(G(1))

        S = set(self.vertices)
        self.G_gens = [self.optimized_rep(g) for g in random_generating_sequence(G)]
        for g in self.G_gens:
            assert all(self.action(g, x) in S for x in S)
        S0 = tuple()
        self.tree = {0: {S0: {'gpel': (S0, self.identity), 'stab': []}}}
        self.scratch = None

    def __getitem__(self, key):
        return self.tree[key]

    def __contains__(self, item):
        return (item in self.tree)

    def depth(self):
        """
        Compute the current depth of the tree.
        """
        return max(self.tree.keys())

    def orbit_rep_recursive(self, mats, n, find_green=True):
        """
        Find the orbit representative for a given tuple.

        This is structured for internal use. Use ``orbit_rep`` instead.
        """
        if n == 0:
            return mats, self.identity
        mats0 = mats[:-1]
        if mats0 in self[n-1] and 'gpel' not in self[n-1][mats0]: # Truncation is an ineligible node
            return None, None
        elif mats0 in self[n-1] and 'stab' in self[n-1][mats0]: # Truncation is a green node
            g0 = self.identity
            y = mats[-1]
            assert y not in mats0
        else: # Truncation needs to be resolved
            mats0, g0 = self.orbit_rep_recursive(mats0, n-1)
            if mats0 is None:
                return None, None
            assert 'gpel' in self[n-1][mats0]
            y = self.action(~g0, mats[-1])
        z, g1 = self[n-1][mats0]['retract'][y]
        assert z not in mats0
        mats1 = mats0 + (z,)
        if not find_green:
            return mats1, g0*g1
        if 'gpel' not in self[n][mats1]: # Found an ineligible node
            return None, None
        mats2, g2 = self[n][mats1]['gpel']
        assert 'gpel' in self[n][mats2]
        return mats2, g0*g1*g2
    
    def orbit_rep(self, mats):
        """
        Find the orbit representative for a given tuple.
        
        The output consists of a pair ``(mats1, g)`` such that the action of `g` on `mats` gives `mats`.
        """
        n = len(mats)
        if n not in self:
            raise ValueError("Tree not computed to depth {}".format(n))
        return self.orbit_rep_recursive(mats, n)

    def green_nodes(self, n):
        r"""
        Return an iterator over green nodes at depth `n`.
        """
        for mats, selfnmats in self[n].items():
            if 'stab' in selfnmats:
                yield mats

    def stabilizer_from_gens(self, mats):
        """
        Compute the stabilizer of a subset of vertices.
        
        We record the order of the group and a short generating sequence.
        """
        n = len(mats)
        selfnmats = self[n][mats]
        if n == 0:
            selfnmats['stab'] = (self.G_order, self.G_gens)
            return None
        retract = self[n-1][mats[:-1]]['retract']
        G1_gap = retract.stabilizer(mats[-1], gap=True)
        G2_gap = G1_gap.ClosureGroup(selfnmats['stab'])
        order = G2_gap.Size().sage()
        optimized_gens = [self.optimized_rep(g) for g in G2_gap.SmallGeneratingSet()]
        selfnmats['stab'] = (order, optimized_gens)

    def construct_children(self, mats):
        """
        Construct the children of a green node using a Cayley group retract.
        """
        n = len(mats)
        vertices = [M for M in self.vertices if M not in mats]
        action = self.action
        order, gens = self[n][mats]['stab']
        retract = CayleyGroupRetract(self.G, vertices, action, self.optimized_rep, gens=gens, order=order)
        self[n][mats]['retract'] = retract
        for M in retract.reps():
            mats1 = mats + (M,)
            if M in mats:
                raise ValueError("Found repeated entry in tuple")
            self[n+1][mats1] = {}

    def nodes_at_new_level(self, verbose=False):
        """
        Compute nodes at a new level of the tree (without classifying them).
        """
        n = self.depth()
        if verbose:
            print("Original depth: {}".format(n))
        self.tree[n+1] = {}
        G = self.G
        check_count = 0
        for mats in self.green_nodes(n):
            self.stabilizer_from_gens(mats)
            order, gens = self[n][mats]['stab']
            if not self.forbid:
                assert self.G_order % order == 0
                check_count += self.G_order // order
            self.construct_children(mats)
            if verbose:
                print("Constructed children of a node with stabilizer order {}".format(order))
        # If no forbidden vertices, check the orbit-stabilizer formula.
        if not self.forbid:
            if check_count != binomial(len(self.vertices), n):
                raise RuntimeError("Error in orbit-stabilizer formula")
        if verbose:
            print("Number of new nodes: {}".format(len(self[n+1])))

    def classify_nodes(self, verbose=False):
        """
        Classify nodes at the last level of the tree.
        """
        exclude = []
        n = self.depth()
        selfn = self[n]
        for mats in list(selfn.keys()):
            if mats not in selfn or 'gpel' in selfn[mats]:
                continue
            tmp = [tuple(mats[n-1 if i==j else j if i==n-1 else i] for i in range(n)) for j in range(n-1)]
            tmp2 = [self.orbit_rep_recursive(i, n, find_green=False) for i in tmp]
            if any(i[0] is None for i in tmp2):
                for j in [(mats, None)] + tmp2:
                    if j[0] is not None:
                        del selfn[j[0]]
            else:
                selfn[mats]['gpel'] = (mats, self.identity)
                selfn[mats]['stab'] = []
                for mats1, g1 in tmp2:
                    if mats1 == mats:
                        selfn[mats]['stab'].append(g1)
                    else:
                        selfn[mats1]['gpel'] = (mats, ~g1)
        if verbose:
            print("Retract computed")
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

