import runpy, numpy as np, itertools
g = runpy.run_path("/tmp/claude-0/-home-user/69126eca-8d7d-5969-ab6e-745654c8c3a5/scratchpad/indep_catalogue.py")
canon, canons, T, from_mul = g["canon"], g["canons"], g["T"], g["from_mul"]
# positive control 1: a relabelled transpose of class 100 is found as class 100
t = T[99].T.copy(); pi = np.array([3,1,5,0,2,4]); inv = np.argsort(pi)
r = pi[t[inv][:, inv]].astype(np.int8)
print("control relabelled transpose of [6,100] ->", canons.get(min(canon(r), canon(r.T.copy()))))
# positive control 2: a non-associative table is flagged
t = T[0].copy(); t[1][1] = 2; t[2][2] = 1
lhs = t[t[:, :, None], np.arange(6)[None, None, :]]; rhs = t[np.arange(6)[:, None, None], t[None, :, :]]
print("control non-assoc flagged:", not np.array_equal(lhs, rhs))
# A2^g: A2 with its zero replaced by the group Z2 = {e, g}
def a2(x, y):
    (i, j), (k, l) = x, y
    return (i, l) if [[1,1],[1,0]][j][k] else None
def mul(x, y):
    grp = {"e": 0, "g": 1}
    if x in grp and y in grp: return ["e","g"][(grp[x]+grp[y]) % 2]
    if x in grp: return x
    if y in grp: return y
    p = a2(x, y); return "e" if p is None else p
t = from_mul(["e","g",(0,0),(0,1),(1,0),(1,1)], mul)
print("A2^g (zero of A2 replaced by Z2) -> class", canons.get(min(canon(t), canon(t.T.copy()))))
