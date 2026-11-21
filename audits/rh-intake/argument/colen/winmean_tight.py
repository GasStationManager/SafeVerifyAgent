import sys
sys.path.insert(0, '.')
from winmean import run
from math import comb
# n=1, M(t) = (t-c)^k written in binomial basis (integer coefficients): tightness check
for p in (5, 7):
    for k in (2, 4):
        Mt = lambda t, k=k: [[(t - 3) ** k]]
        run("powk", Mt, 1, k, p, 0, p**4, k)
