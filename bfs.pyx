from collections import deque

def bfs(neighbors, dict d, v0):
    cdef long c = 1
    cdef long count = 1
    queue = deque()
    queue.append((v0, d[v0]))
    while c:
        w, t = queue.popleft()
        c -= 1
        for x, g in neighbors(w):
            if x not in d:
                u = (t[0], g*t[1])
                d[x] = u
                queue.append((x, u))
                c += 1
                count += 1
    return count

