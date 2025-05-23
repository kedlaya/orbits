def as_immutable(vec):
    """
    Return v after having made it immutable.

    This can be used to generate an immutable vector or matrix in an expression (e.g., in a lambda function).
    """
    vec.set_immutable()
    return vec

def first_nonzero(v):
    for i in v:
        if i:
            return i

def sumprod(gen1, gen2):
    c = None
    for a, b in zip(gen1, gen2):
        if a == 1:
            c = b if c is None else c+b
        elif a:
            c = a*b if c is None else c+a*b
    return as_immutable(c)

def bfs(neighbors, given_keys, iden):
    """
    Perform a depth-first search of a directed graph (specified by ``neighbors``).
    """
    cdef dict d = {}
    cdef long count
    cdef list queue
    for v in given_keys:
        if v in d:
            continue
        d[v] = (iden, None)
        count = 0
        queue = [v]
        while True:
            try:
                w = queue.pop()
            except IndexError:
                break
            count += 1
            for (x, g) in neighbors(w):
                y = d.get(x, None)
                if y is None:
                    d[x] = (g*d[w][-2], None)
                    queue.append(x)
        d[v] = (iden, count)
    return d
    

