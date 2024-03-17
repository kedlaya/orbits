def as_immutable(vec):
    """
    Return v after having made it immutable.

    This can be used to generate an immutable vector or matrix in an expression (e.g., in a lambda function).
    """
    vec.set_immutable()
    return vec

def sumprod(gen1, gen2):
    c = None
    for a, b in zip(gen1, gen2):
        if a == 1:
            c = b if c is None else c+b
        elif a:
            c = a*b if c is None else c+a*b
    return as_immutable(c)

def dfs(neighbors, dict d, v0):
    """
    Perform a depth-first search of a directed graph (specified by ``neighbors``).
    """
    cdef long count = 1
    cdef list queue = [(v0, d[v0])]
    while True:
        try:
            w, t = queue.pop()
        except IndexError:
            d[v0] = d[v0][:2] + (count,)
            break
        for (x, g) in neighbors(w):
            if x not in d or d[x] is None:
                u = (t[0], g*t[1], None)
                d[x] = u
                queue.append((x, u))
                count += 1


