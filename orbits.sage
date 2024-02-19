import random
from collections import deque
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
        for v in exclude:
            forbidden_reps.add(d[v][0])
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
    def __init__(self, G, vertices, apply_group_elem, optimized_rep=None, debug=False, order=None, gens=None):
        self.optimized_rep = optimized_rep if optimized_rep else (lambda g: g)
        self.apply_group_elem = apply_group_elem
        self.G_order = G.order() if order is None else order
        self.gens = [self.optimized_rep(g) for g in random_generating_sequence(G)] if gens is None else gens
        if debug:
            vertex_set = set(vertices)
            assert all(apply_group_elem(g, v) in vertex_set for g in self.gens for v in vertex_set)
        neighbors = lambda M, act=apply_group_elem, gens=self.gens: ((act(g, M), g) for g in gens)
        GroupRetract.__init__(self, G, vertices, neighbors, optimized_rep=optimized_rep)

    def stabilizer_gens(self, v):
        """
        Compute generators of a point stabilizer.
        
        The output consists of a list of elements of ``self``; the same list in the format of
        ``optimized_rep``; and the underlying subgroup as a GAP group.
        """
        mats0, g0 = self[v]
        # Use the orbit-stabilizer formula to compute the stabilizer order.
        orbit_len = self.orbit_len[mats0]
        target_order = ZZ(self.G_order / orbit_len)
        H = G.subgroup([]).gap()
        # Early abort for the trivial group.
        if target_order == 1:
            return [], [], H
        # Produce random stabilizer elements until we hit the right order.
        d = self.d
        orbit = [w for w in self.vertices() if d[w][0] == mats0]

        def random_gen():
            while True:
                e1 = random.choice(orbit)
                mats1, g1 = d[e1]
                assert mats1 == mats0
                rgen = random.choice(self.gens)
                e2 = self.apply_group_elem(rgen, e1)
                mats2, g2 = d[e2]
                assert mats2 == mats0
                g = rgen*g1
                if g != g2:
                    return g0*~g2*g*~g0
  
        stab_gens = []
        stab_gens_in_G = []
        old_order = 1
        while True:
            h = random_gen()
            Gh = self.G(h)
            H = H.ClosureGroup(Gh) # Subgroup of G generated by H and h
            order = H.Size().sage()
            if order == old_order: # Redundant generator, try again
                continue
            stab_gens.append(h)
            stab_gens_in_G.append(Gh)
            if order == target_order: # Done!
                return stab_gens_in_G, stab_gens, H

    def stabilizer(self, v, gens=False):
        """
        Compute a point stabilizer.
        
        If ``gens`` is ``True``, return a list of generators of the stabilizer instead,
        in the format of ``optimized_rep``; a list of the same generators as elements of the
        ambient group; and the order of the stabilizer.
        """
        stab_gens_in_G, _, _ = self.stabilizer_gens(v)
        return G.subgroup(self.stab_gens_in_G)

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
        
        - ``apply_group_elem``: on input of a group element `g` and a vertex `x`, returns the action of `g` on `x`.
          Defaults to ``g*x``.
        - ``stabilizer``: on input of a vertex `x`, returns a group whose intersection with `G` is the stabilizer of `x`.
        - ``optimized_rep``: converts an element of `G` into a representation expected by ``apply_group_elem``.
        - ``forbid``: on input of a tuple, returns ``True`` if the underlying set should be forbidden. This is assumed to be both
          invariant under both the `G`-action and permutation of the tuple.
        """
        self.G = G
        self.G_order = G.order()
        self.vertices = vertices
        if methods is None:
            methods = {}
        self.apply_group_elem = methods['apply_group_elem'] if 'apply_group_elem' in methods else (lambda g, x: g*x)
        self.stabilizer = methods['stabilizer'] if 'stabilizer' in methods else None
        self.optimized_rep = methods['optimized_rep'] if 'optimized_rep' in methods else (lambda g: g)
        self.forbid = methods['forbid'] if 'forbid' in methods else None
        self.identity = self.optimized_rep(G(1))
        S = set(self.vertices)
        self.G_gens = [self.optimized_rep(g) for g in random_generating_sequence(G)]
        for g in self.G_gens:
            assert all(self.apply_group_elem(g, x) in S for x in S)
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
        """
        if n == 0:
            return mats, self.identity
        mats0 = mats[:-1]
        if mats0 in self[n-1] and 'gpel' not in self[n-1][mats0]: # Truncation is an ineligible node
            return None, None
        elif mats0 in self[n-1] and 'stab' in self[n-1][mats0]: # Truncation is a green node
            assert 'retract' in self[n-1][mats0]
            g0 = self.identity
            y = mats[-1]
            assert y not in mats0
        else: # Truncation needs to be resolved
            mats0, g0 = self.orbit_rep_recursive(mats0, n-1)
            if mats0 is None:
                return None, None
            assert 'gpel' in self[n-1][mats0]
            assert 'retract' in self[n-1][mats0]
            y = self.apply_group_elem(~g0, mats[-1])
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
        """
        n = len(mats)
        if n not in self:
            raise ValueError("Tree not computed to depth {}".format(n))
        return self.orbit_rep_recursive(mats, n)

    def green_nodes(self, n):
        r"""
        Return an iterator over green nodes at depth `n`.
        """
        selfn = self[n]
        for mats, selfnmats in selfn.items():
            if 'stab' in selfnmats:
                yield mats

    def stabilizer_from_gens(self, mats):
        """
        Compute the stabilizer of a subset of vertices.
        """
        n = len(mats)
        selfnmats = self[n][mats]
        if n == 0:
            selfnmats['stab'] = (self.G_order, self.G_gens)
            return None
        parent = mats[:-1]
        endgen = mats[-1]
        G0 = self[n-1][parent]['stab']
        if self.stabilizer is not None:
            G1 = G0.intersection(self.stabilizer(endgen))
            gens = G1.gens()
            optimized_gens = [self.optimized_rep(g) for g in random_generating_sequence(G1)]
            G2 = G.subgroup(gens + selfnmats['stab'])
            selfnmats['stab'] = (G2.order(), optimized_gens + selfnmats['stab'])
        else:
            retract = self[n-1][parent]['retract']
            _, optimized_gens, G1_gap = retract.stabilizer_gens(endgen)
            order = G1_gap.ClosureGroup(selfnmats['stab']).Size().sage()
            selfnmats['stab'] = (order, optimized_gens + selfnmats['stab'])

    def construct_children(self, mats, verbose=False):
        """
        Construct the children of a green node using a Cayley group retract.
        """
        n = len(mats)
        vertices = [M for M in self.vertices if M not in mats]
        apply_group_elem = self.apply_group_elem
        order, gens = self[n][mats]['stab']
        retract = CayleyGroupRetract(self.G, vertices, apply_group_elem, self.optimized_rep, gens=gens, order=order)
        self[n][mats]['retract'] = retract
        if verbose:
            print("Retract computed")
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
            print("Current level: {}".format(n))
        self.tree[n+1] = {}
        G = self.G
        check_count = 0
        for mats in self.green_nodes(n):
            self.stabilizer_from_gens(mats)
            order, _ = self[n][mats]['stab']
            if verbose:
                print("Stabilizer computed: order {}".format(order))
            if not self.forbid:
                assert self.G_order % order == 0
                check_count += self.G_order // order
            self.construct_children(mats, verbose)
        # If no forbidden vertices, check the orbit-stabilizer formula.
        if not self.forbid:
            if check_count != binomial(len(self.vertices), n):
                raise RuntimeError("Error in orbit-stabilizer formula")

    def classify_nodes(self, verbose=False):
        """
        Classify nodes at the last level of the tree.
        """
        edges = {}
        exclude = []
        n = self.depth()
        edges = {mats: [] for mats in self[n]}
        if verbose:
            print("Number of new nodes: {}".format(len(self[n])))
        for mats in self[n]:
            tmp = [tuple(mats[n-1 if i==j else j if i==n-1 else i] for i in range(n)) for j in range(n-1)]
            tmp2 = [self.orbit_rep_recursive(i, n, find_green=False) for i in tmp]
            if any(i[0] is None for i in tmp2):
                exclude.append(mats)
                exclude.extend(j[0] for j in tmp2 if j[0] is not None)
            else:
                for j in range(n-1):
                    mats1, g1 = tmp2[j]
                    edges[mats1].append((mats, g1, j))
                    edges[mats].append((mats1, ~g1, None))
        if verbose:
            print("Edges computed")
        neighbors = lambda M, edges=edges: edges[M]
        retract = GroupRetract(self.G, self[n].keys(), neighbors, exclude, self.forbid, optimized_rep=self.optimized_rep)
        if verbose:
            print("Retract computed")
        # Mark nodes as green or red, and record group elements.
        for mats in retract:
            t = retract[mats]
            self[n][mats]['gpel'] = t
            if t[0] == mats:
                self[n][mats]['stab'] = []
        assert all('stab' in self[n][self[n][mats]['gpel'][0]] for mats in self[n] if 'gpel' in self[n][mats])
        self.scratch = (edges, retract)
        if verbose:
            print("Number of new green nodes: {}".format(sum(1 for _ in self.green_nodes(n))))
            print("New level: {}".format(n))
            print()

    def stabilizer_gens(self, verbose=False):
        """
        Compute stabilizer generators from a group retract.
        """
        n = self.depth()
        edges, retract = self.scratch
        selfn = self[n]
        for mats1 in self.green_nodes(n):
            mats0, g1 = retract[mats1]
            assert mats0 == mats1
            gens = selfn[mats0]['stab']
            for mats2, g0, j in edges[mats1]:
                if j is None: # Ignore backwards edges
                    continue
                assert mats0 == retract[mats2][0]
                g2 = retract[mats2][1]
                g = g0*g1
                if g != g2:
                    gens.append(~g2*g)
        if verbose:
            print("Stabilizer generators found")
        self.scratch = None
        
    def extend(self, n, verbose=False):
        r"""
        Extend the tree to a new depth.
        """
        while self.depth() < n:
            if self.scratch:
                self.stabilizer_gens(verbose)
            self.nodes_at_new_level(verbose)
            self.classify_nodes(verbose)

