def as_immutable(vec):
    """
    Return v after having made it immutable.

    This can be used to generate an immutable vector or matrix in an expression (e.g., in a lambda function).
    """
    vec.set_immutable()
    return vec

def dfs(neighbors, dict d, v0):
    """
    Perform a depth-first search of a directed graph (specified by ``neighbors``).
    """
    cdef long c = 0
    cdef long count = 1
    cdef list queue = [(v0, d[v0])]
    while c < count:
        c += 1
        w, t = queue.pop()
        for u in neighbors(w):
            (x, g) = u
            if x not in d:
                u = (t[0], g*t[1], None)
                d[x] = u
                queue.append((x, u))
                count += 1
    return count


