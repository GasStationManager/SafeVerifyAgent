"""NODE-LEAVES, float checks (standard library, python3 -I).

Checks the Lean's *analytic* normalisations in SemiChar.lean (Formalism.L2.Th1.F):
  s2 L      = (wEta w1 * conj w2 - wEta w2 * conj w1) / (w1 conj w2 - w2 conj w1),  wEta(w) = 2 zeta(w/2)
  sgStar    = sigma(z) exp(-s2 z^2/2)
  herm z w  = z conj(w) / area,  area = |Im(conj w1 * w2)|
  opU x F z = F(z+x) exp(-pi herm z x - pi herm x x / 2)
  th0 t z   = opU t sgStar z / opU t sgStar 0
For three CM curves (Z[i]: g2=4,g3=0;  Z[w]: g2=0,g3=-4;  O_{Q(sqrt-7)}: g2=140,g3=392, i.e. y^2=x^3-35x-98):
  (1) s2 (expect 0, 0, and 1 for d=7 -- predicted from alpha(alpha-alphabar)s2 = sum_{P in E[alpha]-0} wp(P), alpha=omega_K);
  (2) K_t(z) := th0_t(z)/sgStar(z) satisfies K_t(z)^2 = wp(z) - wp(t) for 2-torsion t  (Kronecker / co-sigma identity);
  (3) for N-torsion t (N = 3, 5) the multiplier K_t(z+w)/K_t(z) is an N-th root of unity for w in the lattice
      (so K_t^N is elliptic: the input to the Lean's TransPower/TransUnit argument);
  (4) sigma*(alpha z)/sigma*(z)^{N alpha} is lattice-periodic for alpha in O_K (the NormRel function),
      and fails to be periodic if s2 is replaced by s2 + 1.
"""
import cmath, math

PI = math.pi


def eis(tau, K=60):
    q = cmath.exp(2j * PI * tau)
    E2 = 1; E4 = 1; E6 = 1
    for n in range(1, K):
        s1 = sum(d for d in range(1, n + 1) if n % d == 0)
        s3 = sum(d ** 3 for d in range(1, n + 1) if n % d == 0)
        s5 = sum(d ** 5 for d in range(1, n + 1) if n % d == 0)
        qn = q ** n
        E2 -= 24 * s1 * qn; E4 += 240 * s3 * qn; E6 -= 504 * s5 * qn
    return E2, E4, E6


class Lat:
    """Lattice Z W1 + Z W2 (tau = W2/W1 in upper half plane)."""
    def __init__(self, W1, W2, K=60):
        self.W1, self.W2 = W1, W2
        tau = W2 / W1
        assert tau.imag > 0
        E2, E4, E6 = eis(tau, K)
        self.g2 = (4 * PI ** 4 / 3) * E4 / W1 ** 4
        self.g3 = (8 * PI ** 6 / 27) * E6 / W1 ** 6
        self.eta1 = PI ** 2 / (6 * W1) * E2          # zeta(W1/2)
        self.H1 = 2 * self.eta1                       # wEta(W1) = 2 zeta(W1/2)
        self.H2 = (self.H1 * W2 - 2j * PI) / W1       # Legendre: H1 W2 - H2 W1 = 2 pi i
        self.q = cmath.exp(1j * PI * tau)             # nome
        self.K = K

    def sigma(self, z):
        W1, q = self.W1, self.q
        v = cmath.exp(self.eta1 * z * z / W1) * (W1 / PI) * cmath.sin(PI * z / W1)
        c = cmath.cos(2 * PI * z / W1)
        for n in range(1, self.K):
            q2n = q ** (2 * n)
            v *= (1 - 2 * q2n * c + q2n * q2n) / (1 - q2n) ** 2
        return v

    def wp(self, z):
        # wp = -(log sigma)'' via central differences on the product formula is too lossy; use
        # wp(z) = -eta1*2/W1 + (pi/W1)^2 / sin^2(pi z/W1) - 8 (pi/W1)^2 sum n q^{2n}/(1-q^{2n}) cos(2 pi n z/W1)
        W1, q = self.W1, self.q
        a = PI / W1
        v = -2 * self.eta1 / W1 + a * a / cmath.sin(a * z) ** 2
        for n in range(1, self.K):
            q2n = q ** (2 * n)
            v -= 8 * a * a * n * q2n / (1 - q2n) * cmath.cos(2 * n * a * z)
        return v

    # Lean definitions
    def s2(self):
        W1, W2 = self.W1, self.W2
        return (self.H1 * W2.conjugate() - self.H2 * W1.conjugate()) / (W1 * W2.conjugate() - W2 * W1.conjugate())

    def area(self):
        return abs((self.W1.conjugate() * self.W2).imag)

    def sgStar(self, z):
        return self.sigma(z) * cmath.exp(-self.s2() * z * z / 2)

    def herm(self, z, w):
        return z * w.conjugate() / self.area()

    def opU(self, x, F, z):
        return F(z + x) * cmath.exp(-PI * self.herm(z, x) - PI * self.herm(x, x) / 2)

    def th0(self, t, z):
        return self.opU(t, self.sgStar, z) / self.opU(t, self.sgStar, 0)


def make(g2t, g3t, tau):
    """Scale the lattice Z + Z tau so that (g2, g3) = (g2t, g3t)."""
    L0 = Lat(1 + 0j, tau)
    # g2(lam L) = lam^-4 g2(L), g3(lam L) = lam^-6 g3(L)
    if abs(g3t) < 1e-12:
        lam = (L0.g2 / g2t) ** 0.25
    elif abs(g2t) < 1e-12:
        lam = (L0.g3 / g3t) ** (1 / 6)
    else:
        lam = cmath.sqrt((L0.g3 / g3t) / (L0.g2 / g2t))
    # fix the root: try lam * i^k / sixth roots so that both g2, g3 match
    best = None
    for k in range(12):
        lk = lam * cmath.exp(2j * PI * k / 12)
        L = Lat(lk, lk * tau) if (lk * tau / lk).imag > 0 else None
        if L is None: continue
        err = abs(L.g2 - g2t) + abs(L.g3 - g3t)
        if best is None or err < best[0]:
            best = (err, L)
    return best[1]


def main():
    curves = [
        ("Z[i]   y^2=x^3-x      (g2=4,g3=0)", 4, 0, 1j, 1j, 2),        # alpha = 1+i : N = 2
        ("Z[w]   y^2=x^3+1      (g2=0,g3=-4)", 0, -4, cmath.exp(2j * PI / 3), cmath.exp(2j * PI / 3), 1),
        ("O_K,d=7 y^2=x^3-35x-98 (g2=140,g3=392)", 140, 392, (1 + cmath.sqrt(-7)) / 2, (1 + cmath.sqrt(-7)) / 2, 2),
    ]
    for name, g2, g3, tau, om, Nom in curves:
        L = make(g2, g3, tau)
        W1, W2 = L.W1, L.W2
        print("=" * 100)
        print(name)
        print(f"  lattice W1={W1:.12f}  W2={W2:.12f};  g2={L.g2:.10f}  g3={L.g3:.10f}")
        s2 = L.s2()
        print(f"  (1) Lean s2 = {s2:.12f}")
        # sanity: quasi-periodicity of sigma with Lean's wEta
        z0 = 0.13 + 0.07j
        for W, H in ((W1, L.H1), (W2, L.H2)):
            r = L.sigma(z0 + W) / (-cmath.exp(H * (z0 + W / 2)) * L.sigma(z0))
            print(f"      check sigma(z+W) = -exp(wEta(W)(z+W/2)) sigma(z):  ratio = {r:.12f}")
        # (1b) predicted s2 from the norm identity with alpha = (1+sqrt-7)/2 (d=7 only)
        if g2 == 140:
            al = (1 + cmath.sqrt(-7)) / 2
            P = W1 / 2 + W2 / 2  # = lam * conj(al)/2 mod lattice  (kernel of multiplication by al)
            # check al*P in lattice:
            x = al * (W1 * (1 - al) / 2)   # lam*al*abar/2 = lam
            pred = L.wp(W1 * (1 - al) / 2) / (al * (al - al.conjugate()))
            print(f"      predicted s2 = wp(P)/(alpha(alpha-alphabar)), P = W1*abar/2:  {pred:.12f};  "
                  f"wp(P) = {L.wp(W1 * (1 - al) / 2):.10f}")
        # (2) 2-torsion identity
        print("  (2) K_t(z)^2 - (wp(z) - wp(t)) for 2-torsion t, |.|/|wp(z)-wp(t)|:")
        for t in (W1 / 2, W2 / 2, (W1 + W2) / 2):
            errs = []
            for z in (0.11 + 0.05j, -0.2 + 0.17j, 0.31 - 0.08j):
                z = z * abs(W1)
                K = L.th0(t, z) / L.sgStar(z)
                d = L.wp(z) - L.wp(t)
                errs.append(abs(K * K - d) / abs(d))
            print(f"      t={t:.6f}:  max rel err {max(errs):.2e}")
        # (3) multipliers for N-torsion
        print("  (3) multiplier K_t(z+W)/K_t(z) for N-torsion t; printed as (N * arg/2pi) mod 1 (0 = N-th root of unity), |.|-1:")
        for N in (3, 5):
            for (a, b) in ((1, 0), (1, 1), (2, 1)):
                t = (a * W1 + b * W2) / N
                z = (0.07 + 0.04j) * abs(W1)
                K0 = L.th0(t, z) / L.sgStar(z)
                out = []
                for W in (W1, W2):
                    K1 = L.th0(t, z + W) / L.sgStar(z + W)
                    m = K1 / K0
                    fr = (N * cmath.phase(m) / (2 * PI)) % 1
                    fr = min(fr, 1 - fr)
                    out.append(f"{fr:.1e}/{abs(m) - 1:+.1e}")
                print(f"      N={N} t=({a}W1+{b}W2)/N : W1 -> {out[0]},  W2 -> {out[1]}")
        # (4) NormRel function periodicity
        al = {2: None}
        if g2 == 4 and g3 == 0:
            alphas = [(1 + 1j, 2), (2 + 1j, 5), (2, 4)]
        elif g2 == 0:
            w = cmath.exp(2j * PI / 3)
            alphas = [(1 - w, 3), (2 + w, 3), (2, 4)]
        else:
            w = (1 + cmath.sqrt(-7)) / 2
            alphas = [(w, 2), (1 + w, 4), (2, 4)]
        print("  (4) f(z) = sigma*(alpha z)/sigma*(z)^N  :  |f(z+W)/f(z) - 1| with Lean s2, and with s2+1")
        for a, N in alphas:
            for ds in (0, 1):
                s2x = s2 + ds
                def sg(z, s2x=s2x):
                    return L.sigma(z) * cmath.exp(-s2x * z * z / 2)
                z = (0.09 + 0.05j) * abs(W1)
                f0 = sg(a * z) / sg(z) ** N
                rs = []
                for W in (W1, W2):
                    f1 = sg(a * (z + W)) / sg(z + W) ** N
                    rs.append(abs(f1 / f0 - 1))
                print(f"      alpha={a:.4f} N={N} s2{'+1' if ds else '  '}:  {rs[0]:.2e}  {rs[1]:.2e}")


if __name__ == "__main__":
    main()
