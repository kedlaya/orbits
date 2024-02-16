def bfs(neighbors, dict d, v0):
    cdef long c = 0
    cdef long count = 1
    cdef list queue = [(v0, d[v0])]
    while c < count:
        c += 1
        w, t = queue.pop()
        for x, g in neighbors(w):
            if x not in d:
                u = (t[0], g*t[1])
                d[x] = u
                queue.append((x, u))
                count += 1
    return count

