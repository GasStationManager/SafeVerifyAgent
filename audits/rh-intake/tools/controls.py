"""Negative controls: each port must say False on a mutated input. Usage: controls.py <src-root>"""
import sys, io, contextlib, importlib.util, re
root = sys.argv[1]
def load(name):
    spec = importlib.util.spec_from_file_location(name, __file__.rsplit('/', 1)[0] + f'/{name}.py')
    m = importlib.util.module_from_spec(spec)
    old = sys.argv; sys.argv = [name, root]
    with contextlib.redirect_stdout(io.StringIO()):
        try: spec.loader.exec_module(m)
        except SystemExit: pass
    sys.argv = old; return m
L = load('recompute_loops'); P = load('recompute_primes'); E = load('recompute_example')
f13 = L.fact(13)
tab2 = [list(r) for r in L.tab]; tab2[3] = (tab2[3][0], tab2[3][1], tab2[3][2], tab2[3][3], tab2[3][4][:-1] + [tab2[3][4][-1] + 2])
tab3 = L.tab[:5] + L.tab[6:]
c = {
 'PC.loop started with 2000 extra primes':   L.pc_loop(362, 131070, 2, 0, 1) and not L.pc_loop(362, 131070, 2, 2000, 1),
 'run1 with wrong final prime count':       not L.run(32768, 1613, 32766, 2, 1),
 'run2 started from wrong count':           not L.run(65536, 3030, 32768, 32768, 1611),
 'ladder with bound 1/2 instead of 1/20':    True,   # replaced below
 'table with one composite entry':          not L.okAll(100, tab2, 16900),
 'table with a row removed':                not L.okAll(100, tab3, 16900),
 'lcmUpto <= 2^n is false below 30':         not all(L.lcmUpto(n) <= 2**n for n in range(30)),
 'is_prime rejects a Carmichael number':    not P.is_prime(561) and not P.is_prime(413718278401 * 603339156001),
 'lucas rejects a wrong witness list':      not all(E.lucas(E.t1, 5, 63, [(2,10),(3,4),(571,2),(599,2)]).values()),
 'lucas rejects short fuel':                not all(E.lucas(E.t1, 5, 62, [(2,10),(3,4),(571,2),(599,3)]).values()),
 'ndPowMod agrees with pow on 200 inputs':  all(E.ndPowMod(E.t2, 74, a, e) == pow(a, e, E.t2) for a in range(2, 12) for e in range(E.t2 - 20, E.t2)),
}
orig = L.chk
L.chk = lambda M, F, r, a, b: M <= 2 * L.bsum(lambda p: L.term(M, F, r, a, b, p), a.bit_length()-1, b//2)
c['ladder with bound 1/2 instead of 1/20'] = not L.ladder(10**9, f13, 13, 196, 60, 100); L.chk = orig
for k, v in c.items(): print(f'{k:42}', 'control fires' if v else 'CONTROL DID NOT FIRE')
sys.exit(0 if all(c.values()) else 1)
