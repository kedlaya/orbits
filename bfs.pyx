def dfs(neighbors, dict d, v0):
    cdef long c = 0
    cdef long count = 1
    cdef list queue = [(v0, d[v0])]
    while c < count:
        c += 1
        w, t = queue.pop()
        for u in neighbors(w):
            (x, g) = u[:2]
            if x not in d:
                u = (t[0], g*t[1])
                d[x] = u
                queue.append((x, u))
                count += 1
    return count

def mult_immutable(mat, vec):
    ans = mat*vec
    ans.set_immutable()
    return ans

