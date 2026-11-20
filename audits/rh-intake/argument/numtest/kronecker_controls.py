"""Perturbation controls for the Kronecker-theta valuation law (curve Z[i], p = 7 inert, a < 600, b <= 16).
Perturb one Hurwitz-type input Phi_m (m = 12, i.e. the w^10 coefficient of wp) by d in the p-adic engine and
report how the statistics against EMP / LB change.  A correct pipeline must show the law breaking."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from kronecker_lib import phi_numbers, rows_padic, N_val, vp_fact

p, L, m = 7, 600, 16
gam, rho = p / (p * p - 1), 1 / (p * p - 1)
Phi = phi_numbers(4, 0, L + m + 6)
K = int(L / (p - 1)) + 80
out = []
import random
from fractions import Fraction
from kronecker_lib import vpF
random.seed(2)
# 'scrambled' input: Phi_n -> p^{v_p(Phi_n)} * (random p-adic unit): keeps every one-variable valuation, destroys all
# arithmetic relations between the Hurwitz-type numbers.  If the two-variable law survives, it is a formal consequence
# of the one-variable law v(Phi_n) ~ gamma*n plus the binomial-convolution structure.
def unit():
    while True:
        u = random.randrange(1, p ** K)
        if u % p: return u
Scr = [Fraction(0) if x == 0 else Fraction(p) ** vpF(x, p) * unit() for x in Phi]
for label, inp, pert in [('unperturbed', Phi, None), ('Phi_12 += 1', Phi, (12, 1)), ('Phi_200 += 1', Phi, (200, 1)),
                         ('Phi_400 += 1', Phi, (400, 1)), ('Phi_400 += 7^20', Phi, (400, 7 ** 20)),
                         ('scrambled units', Scr, None)]:
    rows, h = rows_padic(inp, p, K, [L + 2] * (m + 2), perturb=pert)
    de, db, n = [], [], 0
    for b in range(1, m + 1):
        for a in range(50, L):
            if (a + b) % 4: continue
            v, ok = N_val(rows, h, a, b, p, K)
            de.append(v - max(gam * (a + b) - b, rho * (a + b)))
            db.append(v - (vp_fact(a, p) + vp_fact(b - 1, p) - rho * (a + b) - min(b, (a + b) / (p + 1))))
    out.append(f'{label:16s}: v-EMP in [{min(de):7.2f}, {max(de):7.2f}] mean {sum(de)/len(de):7.2f};  '
               f'#(v < LB) = {sum(1 for x in db if x < 0)} of {len(db)}')
print('\n'.join(out))
open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'out_kronecker_controls.txt'), 'w').write('\n'.join(out) + '\n')

# second block: Z[w], p = 5, a < 300, b <= 40 (covers the plateau b >= a/p and the balanced corner a ~ b)
p, L, m, dd = 5, 300, 40, 6
gam, rho = p / (p * p - 1), 1 / (p * p - 1)
Phi = phi_numbers(0, 4, L + m + 6); K = int(L / (p - 1)) + 80
Scr = [Fraction(0) if x == 0 else Fraction(p) ** vpF(x, p) * unit() for x in Phi]
out2 = ['', 'Z[w], p = 5, a < 300, b <= 40: v - EMP by regime (capped: b < a/p; plateau: b >= a/p)']
for label, inp in [('unperturbed', Phi), ('scrambled units', Scr)]:
    rows, h = rows_padic(inp, p, K, [L + 2] * (m + 2))
    cap, pla, same = [], [], []
    for b in range(1, m + 1):
        for a in range(0, L):
            if (a + b) % dd or a + b < 20: continue
            v, ok = N_val(rows, h, a, b, p, K)
            d = v - max(gam * (a + b) - b, rho * (a + b))
            (cap if b < a / p else pla).append(d)
            same.append(v)
    if label == 'unperturbed': ref = same
    agree = sum(1 for x, y in zip(ref, same) if x == y)
    out2.append(f'{label:16s}: capped [{min(cap):.2f}, {max(cap):.2f}] mean {sum(cap)/len(cap):.2f};  '
                f'plateau [{min(pla):.2f}, {max(pla):.2f}] mean {sum(pla)/len(pla):.2f};  identical v: {agree}/{len(same)}')
print('\n'.join(out2))
open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'out_kronecker_controls.txt'), 'a').write('\n'.join(out2) + '\n')
