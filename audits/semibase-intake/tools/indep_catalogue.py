"""Independent check of the Lean catalogue data (audit, not the repo's script).
Parses SemiBase/Catalogue/Order6/Part*.lean directly (all lines, not a single regex
on def lines), and checks: every part file has only the expected kinds of lines;
each partNNN list is exactly S6_a..S6_b in order with no inline entries; 6x6
tables with entries 0..5; associativity; ids 1..15973 in order; pairwise
non-isomorphic AND non-anti-isomorphic (canonical form over 720 perms x
{T, T^T}); self-dual count; the four exceptional classes vs independently
constructed B2^1, A2^1, L (Zhang-Luo presentation)."""
import glob, re, itertools, sys
import numpy as np
ROOT = "/home/user/semibase-order6"
DEF = re.compile(r"^def S6_(\d+) : Entry := ⟨(\d+), (\[\[[0-9, \[\]]*\]\])⟩$")
entries = {}
lists = []
bad_lines = []
for path in sorted(glob.glob(ROOT + "/SemiBase/Catalogue/Order6/Part*.lean")):
    text = open(path, encoding="utf-8").read()
    m = re.search(r"def (part\d+) : List Entry :=\s*\[(.*?)\]\s*\nend SemiBase", text, re.S)
    assert m, path
    names = [s.strip() for s in m.group(2).split(",")]
    assert all(re.fullmatch(r"S6_\d+", n) for n in names), path
    lists.append((m.group(1), [int(n[3:]) for n in names]))
    body = text[: m.start()]
    for line in body.splitlines():
        d = DEF.match(line)
        if d:
            k, i, rows = int(d.group(1)), int(d.group(2)), eval(d.group(3))
            assert k not in entries, k
            entries[k] = (i, rows)
        elif line.strip() and not (line.startswith("/--") or line.startswith("import SemiBase.Statement")
              or line.startswith("namespace SemiBase.Catalogue.Order6") or line in ("/-!", "-/")
              or line.startswith("# Catalogue of order six") or line.startswith("Multiplication tables of GAP")
              or line.startswith("elements `0") or line.startswith("`scripts/generate_census.py`")):
            bad_lines.append((path, line))
print("unexpected lines:", bad_lines[:5], len(bad_lines))
order = [k for _, ks in lists for k in ks]
print("parts:", len(lists), "listed:", len(order), "defs:", len(entries))
assert order == list(range(1, 15974)), "list order"
assert all(entries[k][0] == k for k in order), "id field"
T = np.zeros((15973, 6, 6), dtype=np.int8)
for k in order:
    rows = entries[k][1]
    assert len(rows) == 6 and all(len(r) == 6 for r in rows) and all(0 <= x <= 5 for r in rows for x in r), k
    T[k - 1] = rows
# associativity
nonassoc = []
for idx in range(15973):
    t = T[idx]
    lhs = t[t[:, :, None], np.arange(6)[None, None, :]]  # (a*b)*c : t[t[a,b], c]
    rhs = t[np.arange(6)[:, None, None], t[None, :, :]]  # a*(b*c) : t[a, t[b,c]]
    if not np.array_equal(lhs, rhs):
        nonassoc.append(idx + 1)
print("non-associative tables:", nonassoc[:5], len(nonassoc))
perms = np.array(list(itertools.permutations(range(6))), dtype=np.int8)
inv = np.argsort(perms, axis=1).astype(np.int8)
P = len(perms)
def canon(t):
    # T'[i][j] = pi(T[pi^-1 i][pi^-1 j])
    r = t[inv[:, :, None], inv[:, None, :]]          # (P,6,6)
    r = np.take_along_axis(perms[:, None, :].repeat(6, 1), r.astype(np.int64), axis=2)
    flat = r.reshape(P, 36)
    i = np.lexsort(flat.T[::-1])[0]
    return flat[i].tobytes()
canons = {}
selfdual = 0
dups = []
for idx in range(15973):
    a = canon(T[idx]); b = canon(T[idx].T.copy())
    if a == b: selfdual += 1
    c = min(a, b)
    if c in canons: dups.append((canons[c], idx + 1))
    canons[c] = idx + 1
print("classes up to iso/anti-iso:", len(canons), "duplicates:", dups[:5], "self-dual:", selfdual)
# independent constructions of exceptional semigroups
def from_mul(elts, mul):
    n = len(elts); ix = {e: i for i, e in enumerate(elts)}
    return np.array([[ix[mul(x, y)] for y in elts] for x in elts], dtype=np.int8)
def rees(P_):  # 0-Rees matrix semigroup over trivial group, 2x2, plus adjoined identity
    elts = ["1", "0"] + [(i, j) for i in range(2) for j in range(2)]
    def mul(x, y):
        if x == "1": return y
        if y == "1": return x
        if x == "0" or y == "0": return "0"
        (i, j), (k, l) = x, y
        return (i, l) if P_[j][k] else "0"
    return from_mul(elts, mul)
B21 = rees([[1, 0], [0, 1]]); A21 = rees([[1, 1], [1, 0]])
def L_mul(x, y):  # Zhang-Luo L = <a,b | a^2=a, b^2=b, aba=0>
    if x == "0" or y == "0": return "0"
    w = x + y
    w = re.sub(r"a+", "a", re.sub(r"b+", "b", w))
    return "0" if "aba" in w else w
Lt = from_mul(["0", "a", "b", "ab", "ba", "bab"], L_mul)
for name, t, k in [("B2^1", B21, 8564), ("A2^1", A21, 13747), ("L", Lt, 3843)]:
    c = min(canon(t), canon(t.T.copy()))
    print(name, "-> catalogue class", canons.get(c), "(claimed", k, ")")
