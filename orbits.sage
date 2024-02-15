import random
from collections import deque

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

def retract_from_graph(iden, Gamma, reps, forward_only=False):
    """
    Compute a group retract from a generalized Cayley digraph.
    
    Set ``forward_only`` to `True` only if it is known that every weakly connected component
    is strongly connected (e.g., for a true Cayley digraph).
    """
    l = [(M, (M, iden)) for M in reps]
    d = dict(l)
    queue = deque(l)
    while queue:
        M, (dM0, dM1) = queue.popleft()
        for (_, M1, g) in Gamma.outgoing_edge_iterator(M):
            if M1 not in d:
                t = (dM0, g*dM1)
                d[M1] = t
                queue.append((M1, t))
        if not forward_only:
            for (M1, _, g) in Gamma.incoming_edge_iterator(M):
                if M1 not in d:
                    t = (dM0, ~g*dM1)
                    d[M1] = t
                    queue.append((M1, t))
    return d

# Given a generalized Cayley graph for a group G acting (on the left) on a set of vertices, 
# return a list of connected component representatives not containing any vertices 
# listed in `exclude` or any vertices for which `forbid` returns True, and a dictionary 
# identifying group elements carrying representatives to arbitrary vertices in their components.

class GroupRetract():
    """
    Group retract object associated to a group action and a generalized Cayley digraph.
    
    The underlying dict is stored as the attribute ``d``, but one can also index directly.
    """
    def __init__(self, G, vertices, edges, exclude=[], forbid=None, forward_only=False, optimized_rep=None):
        self.G = G
        vertices = list(vertices)
        self.optimized_rep = optimized_rep if optimized_rep else (lambda g: g)
        # Early abort if there are no edges and nothing to exclude (e.g., a Cayley digraph for the trivial group).
        if not edges and not exclude and not forbid:
           iden = optimized_rep(G(1)) if optimized_rep else G(1)
           self.d = {v: (v, iden) for v in vertices}
           self.forbidden_verts = set()
           return None
        # Add dummy edges to link all excluded vertices.
        edges2 = [(exclude[0], exclude[i]) for i in range(1, len(exclude))]
        # Construct the digraph.
        Gamma = DiGraph([vertices, edges + edges2], loops=True, format='vertices_and_edges')
        # Check that we did not implicitly add any vertices.
        assert set(Gamma.vertices(sort=False)) == set(vertices)
        # Remove all vertices connected to an excluded vertex.
        if exclude:
            forbidden_verts = Gamma.connected_component_containing_vertex(exclude[0], sort=False)
            Gamma.delete_vertices(forbidden_verts)
        else:
            forbidden_verts = []
        # Compute connected components.
        conn = Gamma.connected_components(sort=False)
        # Remove all components containing a forbidden vertex.
        reps = []
        for l in conn:
            i = l[0]
            if forbid and forbid(i):
                forbidden_verts += l
            else:
                reps.append(i)
        # Compute the retract on the remaining components.
        iden = self.optimized_rep(G(1))
        d = retract_from_graph(iden, Gamma, reps, forward_only)
        # Check that we are not missing any vertices.
        forbidden_verts = set(forbidden_verts)
        assert all(M in d or M in forbidden_verts for M in vertices)
        self.d = d

    def __getitem__(self, key):
        return self.d[key]

    def __iter__(self):
        return self.d.__iter__()

    def __contains__(self, item):
        return (item in self.d)

    def vertices(self):
        return self.d.keys()
        
    def reps(self):
        for v in self.d.keys():
            if self[v][0] == v:
                yield v

class CayleyGroupRetract(GroupRetract):
    """
    Specialized version of GroupRetract for Cayley digraphs.
    """
    def __init__(self, G, vertices, apply_group_elem, optimized_rep=None):
        self.optimized_rep = optimized_rep if optimized_rep else (lambda g: g)
        gens = [self.optimized_rep(g) for g in random_generating_sequence(G)]
        self.gens = gens
        vertex_set = set(vertices)
        self.apply_group_elem = apply_group_elem
        assert all(apply_group_elem(g, v) in vertex_set for g in gens for v in vertex_set)
        edges = [(M, apply_group_elem(g, M), g) for g in gens for M in vertices]
        GroupRetract.__init__(self, G, vertices, edges, forward_only=True, optimized_rep=optimized_rep)

    def stabilizer_gens(self, v):
        """
        Compute generators of a point stabilizer.
        """
        mats0, g0 = self[v]
        vertices = tuple(self.vertices())
        # Use the orbit-stabilizer formula to compute the stabilizer order.
        orbit_len = sum(1 for e0 in self if e0 in self and self[e0][0] == mats0)
        target_order = ZZ(self.G.order() / orbit_len)
        # Produce random stabilizer elements until we hit the right order.
        gens = []
        while target_order > 1:
            e1 = random.choice(vertices)
            mats1, g1 = self[e1]
            if mats1 != mats0:
                continue
            rgen = random.choice(self.gens)
            e2 = self.apply_group_elem(rgen, e1)
            mats2, g2 = self[e2]
            assert mats2 == mats0
            g = rgen*g1
            if g != g2:
                gens.append(g0*~g2*g*~g0)
                if self.G.subgroup(gens).order() == target_order:
                     break
        return gens

    def stabilizer(self, v):
        """
        Compute a point stabilizer.
        """
        return self.G.subgroup(self.stabilizer_gens(v))

# The data structure for orbit lookup trees of depth $n$:
# - The tree is a dictionary `tree` indexed by levels $0, \dots, n$.
# - Each level `tree[k]` is a dictionary keyed by a $k$-tuple, identified with nodes of the tree.
# - Each value `tree[k][U]` is a dictionary with the following keys:
#  - `gpel` (for $U$ eligible): a pair $(U', g)$ such that $U'$ is a green node and $g(U') = U$.
#  - `stab` (for $U$ green) the stabilizer of $U$.
#  - `retract` (for $U$ green and $k<n$): a dictionary whose value at $y \in S \setminus U$ (resp $y \in S/U$) is an element $g \in G_U$ such that $U \cup \{g^{-1}(y)\}$ (resp. $\pi_U^{-1}(g^{-1}(y))$) is a red or green node.

class OrbitLookupTree():
    def __init__(self, G, vertices, methods):
        self.G = G
        self.vertices = vertices
        self.apply_group_elem = methods['apply_group_elem']
        self.stabilizer = methods['stabilizer'] if 'stabilizer' in methods else None
        self.optimized_rep = methods['optimized_rep'] if 'optimized_rep' in methods else (lambda g: g)
        self.forbid = methods['forbid'] if 'forbid' in methods else (lambda x, easy=False: False)
        S0 = tuple()
        self.tree = {0: {S0: {'gpel': (S0, self.optimized_rep(G(1))), 'stab': []}}}
        self.scratch = None

    def __getitem__(self, key):
        return self.tree[key]

    def __contains__(self, item):
        return (item in self.tree)

    def depth(self):
        return max(self.tree.keys())

    def orbit_rep(self, mats, find_green=True):
        """
        Find the orbit representative for a given tuple.
        """
        n = len(mats)
        tree = self.tree
        G = self.G
        if n not in tree:
            raise ValueError("Tree not computed to depth {}".format(n))
        if n == 0:
            return mats, self.optimized_rep(G(1))
        mats0 = mats[:-1]
        if mats0 in tree[n-1] and 'gpel' not in tree[n-1][mats0]: # Truncation is an ineligible node
            return None, None
        elif mats0 in tree[n-1] and 'stab' in tree[n-1][mats0]: # Truncation is a green node
            assert 'retract' in tree[n-1][mats0]
            g0 = self.optimized_rep(G(1))
            y = mats[-1]
            assert y not in mats0
        else: # Truncation needs to be resolved
            mats0, g0 = self.orbit_rep(mats0, find_green=True)
            if mats0 is None:
                return None, None
            assert 'gpel' in tree[n-1][mats0]
            assert 'retract' in tree[n-1][mats0]
            y = self.apply_group_elem(~g0, mats[-1])
        z, g1 = tree[n-1][mats0]['retract'][y]
        assert z not in mats0
        mats1 = mats0 + (z,)
        if not find_green:
            return mats1, g0*g1
        if 'gpel' not in tree[n][mats1]:
            return None, None
        mats2, g2 = tree[n][mats1]['gpel']
        assert 'gpel' in tree[n][mats2]
        return mats2, g0*g1*g2

    def green_nodes(self, n):
        """
        Return a list of green nodes at depth n.
        """
        return [mats for mats in self[n] if 'stab' in self[n][mats]]

    def nodes_at_new_level(self, verbose=False):
        n = self.depth()
        if verbose:
            print("Current level: {}".format(n))
        if self.scratch:
            self.stabilizer_gens(verbose)
        self.tree[n+1] = {}
        G = self.G
        for mats in self[n]:
            if 'stab' in self[n][mats]: # Green node
                # Compute the stabilizer of mats (deferred from the previous level).
                if n == 0:
                    G0 = G
                    gens = list(G0.gens())
                else:
                    parent = mats[:-1]
                    endgen = mats[-1]
                    G0 = self[n-1][parent]['stab']
                    if G0.order() == 1:
                        gens = []
                    elif self.stabilizer is not None:
                        G0 = G0.intersection(self.stabilizer(endgen))
                        gens = list(G0.gens())
                    else:
                        retract = self[n-1][parent]['retract']
                        gens = retract.stabilizer_gens(endgen)
                G1 = G.subgroup(gens + self[n][mats]['stab'])
                self[n][mats]['stab'] = G1
                if verbose:
                    print("Stabilizer order: {}".format(G1.order()))
                vertices = [M for M in self.vertices if M not in mats]
                # Construct the Cayley group retract under this green node.
                retract = CayleyGroupRetract(G1, vertices, self.apply_group_elem, self.optimized_rep)
                self[n][mats]['retract'] = retract
                if verbose:
                    print("Retract computed")
                for M in retract.reps():
                    if M in mats:
                        raise ValueError("Found repeated entry in tuple")
                    mats1 = mats + (M,)
                    self[n+1][mats1] = {}
        # If no forbidden vertices, check the orbit-stabilizer formula.
        if not self.forbid:
            N = G.order()
            if not sum(N // self[n][mats]['stab'].order() for mats in self[n] if 'stab' in self[n][mats]) == binomial(len(S), n):
                raise RuntimeError("Error in orbit-stabilizer formula")
        if verbose:
            print("Number of new nodes: {}".format(len(self[n+1])))
            print()

    def identify_green(self, verbose=False):
        edges = []
        exclude = []
        n = self.depth()
        for mats in self[n]:
            if self.forbid(mats, easy=True):
                exclude.append(mats)
            else:
                tmp = [tuple(mats[n-1 if i==j else j if i==n-1 else i] for i in range(n)) for j in range(n-1)]
                for i in tmp:
                    mats1, g1 = self.orbit_rep(i, find_green=False)
                    if mats1 is None:
                        exclude.append(mats)
                    else:
                        edges.append((mats1, mats, g1))
        if verbose:
            print("Edges computed")
        retract = GroupRetract(self.G, self[n].keys(), edges, exclude, self.forbid)
        if verbose:
            print("Retract computed")
        # Mark nodes as green or red, and record group elements.
        for mats in retract:
            t = retract[mats]
            self[n][mats]['gpel'] = t
            if t[0] == mats:
                self[n][mats]['stab'] = []
        assert all('stab' in self[n][self[n][mats]['gpel'][0]] 
                   for mats in self[n] if 'gpel' in self[n][mats])
        self.scratch = (edges, retract)

    def stabilizer_gens(self, verbose=False):
        n = self.depth()
        edges, retract = self.scratch
        for e in edges:
            if e[0] in retract:
                mats1, g1 = retract[e[0]]
                mats2, g2 = retract[e[1]]
                assert mats1 == mats2
                g = e[2]*g1
                if g != g2:
                    self[n][mats1]['stab'].append(~g2*g)
        if verbose:
            print("Stabilizer generators found")
        self.scratch = None
        
    def extend(self, n, verbose=False):
        while self.depth() < n:
            self.nodes_at_new_level(verbose)
            self.identify_green(verbose)

# Legacy interface for backward compatibility

# Given an orbit lookup tree at depth $n$ (for the action of a finite group $G$ on a finite set $S$), extend it in place
# to depth $n+1$. For $n=0$, pass for `tree` an empty dict and it will be initialized correctly.
#
# The argument `methods` is a dictionary containing functions as specified:
# - `apply_group_elem`: given a pair $(g, x) \in G \times S$, returns $g(x)$.
# - `stabilizer` (optional): given $x \in S$, returns a group whose intersection with $G$ (in some ambient group) is $G_x$. If omitted, we instead use data from the group retract computation to find stabilizers.
# - `optimized_rep` (optional): given an element $g \in G$, return an optimized representation of $g$.
# - `forbid` (optional): given a tuple $(x_1,\dots,x_k)$, return True if the underlying subset $\{x_1,\dots,x_k\}$ is forbidden. It is assumed that this function is symmetric in the tuple and $G$-invariant. If some of these checks are time-consuming, only run them when the optional argument `easy` is True.

def extend_orbit_tree(G, S, outtree, methods, verbose=True, terminate=False):
    apply_group_elem = outtree.apply_group_elem
    stabilizer = outtree.stabilizer
    optimized_rep = outtree.optimized_rep
    forbid = outtree.forbid
    tree = outtree.tree
    n = outtree.depth()
    outtree.extend(n+1, verbose)

    # Defer the computation of stabilizers, recording some elements read off of the graph.
    if terminate:
        if verbose:
            print("Stabilizer generators not computed")
    else:
        outtree.stabilizer_gens(verbose)
    if verbose:
        print("Number of new green nodes: {}".format(sum(1 for mats in tree[n+1] 
                                                     if 'stab' in tree[n+1][mats])))
        print("New level: {}".format(max(tree.keys())))
        print()

# Build an orbit lookup tree to depth n. By default, we do not record stabilizer generators at depth n,
# so the result cannot be used to extend to depth n+1; set terminate=False to override this.
# The semantics of methods are as in extend_orbit_tree.

def build_orbit_tree(G, S, n, methods, verbose=True, terminate=True):    
    outtree = OrbitLookupTree(G, S, methods)
    apply_group_elem = methods['apply_group_elem']
    optimized_rep = methods['optimized_rep'] if 'optimized_rep' in methods else lambda g: g
    # Verify that each generator of G defines a permutation of S.
    for g in G.gens():
        gm = optimized_rep(g)
        Sg = [apply_group_elem(gm, x) for x in S]
        assert set(S) == set(Sg)
    for i in range(n):
        outtree.extend(i+1, verbose)
#        extend_orbit_tree(G, S, outtree, methods, verbose=verbose, terminate=(terminate and (i == n-1)))
    return outtree

# Return a list of green nodes at depth n.
def green_nodes(tree, n):
    return tree.green_nodes(n)

# Use an enhanced $n$-orbit tree to identify an orbit representative for the action of the group $G$ on $k$-tuples.

def orbit_rep_from_tree(G, tree, mats, apply_group_elem, optimized_rep, find_green=True):
    return tree.orbit_rep(mats, find_green)

