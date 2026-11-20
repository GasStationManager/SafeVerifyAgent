"""Recompute the arithmetic facts about the explicit example parameters in
Formalism/LocalToGlobal/Columns/CyclotomicIsCyclotomicExtension.lean. Usage: <src-root>"""
import sys, re, math, random
src = open(sys.argv[1] + '/Formalism/LocalToGlobal/Columns/CyclotomicIsCyclotomicExtension.lean', encoding='utf-8').read()
g = lambda name: int(re.search(r'def %s : ℕ := (\d+)' % name, src)[1])
t1, t2, T, C, N = map(g, ['toyFirstParameter', 'toySecondParameter', 'nd2T', 'columnDegreeBound', 'nd2N'])
q, d, e = 571, 599, 2; condN = 2**(e+2) * q * d          # condN e q d := 2^(e+2)*q*d ; H0 has q=571, d=599, e=2
def mr(n):
    if n < 2: return False
    for p in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if n % p == 0: return n == p
    dd, s = n-1, 0
    while dd % 2 == 0: dd //= 2; s += 1
    r = random.Random(7)
    for a in [2,3,5,7,11,13,17,19,23,29,31,37] + [r.randrange(2, n-1) for _ in range(40)]:
        x = pow(a, dd, n)
        if x in (1, n-1): continue
        for _ in range(s-1):
            x = x*x % n
            if x == n-1: break
        else: return False
    return True
def ndPowMod(m, f, a, e):      # the artifact's own recursion, to check it against pow()
    if f == 0: return 1
    return (a if e % 2 == 1 else 1) * ndPowMod(m, f-1, a*a % m, e//2) % m
def lucas(p, a, f, L):
    prod = math.prod(x**k for x, k in L)
    return dict(prime_bases=all(mr(x) for x, _ in L), prod=prod == p-1, fuel=p-1 < 2**f,
                fermat=ndPowMod(p, f, a, p-1) == 1 == pow(a, p-1, p),
                orders=all(ndPowMod(p, f, a, (p-1)//x) % p != 1 for x, _ in L), mr=mr(p))
checks = {
 'toyFirst lucas':  lucas(t1, 5, 63, [(2,10),(3,4),(571,2),(599,3)]),
 'toySecond lucas': lucas(t2, 5, 74, [(2,24),(3,2),(571,2),(599,3)]),
 'nd2T lucas':      lucas(T, 5, 614, [(2,12),(3,4),(13,2),(571,2),(599,3),(t1,4),(t2,4)]),
 'colDeg lucas':    lucas(C, 5, 616, [(2,12),(3,4),(23,2),(571,2),(599,3),(t1,4),(t2,4)]),
 'norm forms': dict(t1=1 + d*(condN*18)**2 == t1, t2=1 + d*(condN*768)**2 == t2,
                    T=1 + d*(condN*(t1*t2)**2*468)**2 == T, C=1 + d*(condN*(t1*t2)**2*828)**2 == C),
 'identities': dict(a=-((t1-1)//2)*2 + t1 == 1, b=-((t2-1)//2)*2 + t2 == 1, c=-((T-1)//2)*2 + T == 1, d=-((C-1)//2)*2 + C == 1),
 'congruences': dict(t1=t1 % condN == 1, t2=t2 % condN == 1, T=T % condN == 1, C=C % condN == 1, mod4=t1 % 4 == 1 == t2 % 4),
 'distinct': dict(x=len({t1, t2, T, C}) == 4, gt16=t1 > 16 < t2),
 'level': dict(t1=N % t1 == 0, t2=N % t2 == 0, t1m=N % (t1-1) == 0, t2m=N % (t2-1) == 0, T=N % T == 0, C=N % C == 0, condN=N % condN == 0),
 'nondiv': dict(a=(condN*18) % t1 != 0, b=(condN*768) % t2 != 0),
}

# --- Development/.../Foundations/FoundationsPrimeFact.lean: siteGood_prime_torsion (prime_of_cert _ 5 320 8 [...])
P = 1 + 599 * (123 * (16 * 571 * 599 * (10944929 * 128860109809) ** 2)) ** 2
PL = [2, 3, 41, 571, 599, 10944929, 128860109809]
def powMod(a, m, k, e):    # Nat.rec (fun _ => 1) (fun _ ih e => (ih (e/2)^2 * a^(e%2)) % m) k
    return 1 if k == 0 else (powMod(a, m, k-1, e//2) ** 2 * a ** (e % 2)) % m
checks['siteGood cert'] = dict(lt=P < 2**320, dvd=(math.prod(PL)**8) % (P-1) == 0, bases=all(mr(q) for q in PL),
    fermat=powMod(5, P, 320, P-1) % P == 1 == pow(5, P-1, P), orders=all(powMod(5, P, 320, (P-1)//q) % P != 1 for q in PL),
    ne=P not in (328347841, 1395478321), mr=mr(P))
bad = 0
for k, v in checks.items():
    ok = all(v.values()); bad += not ok
    print(f'{k:18}', 'OK ' if ok else 'FAIL', '' if ok else v)
print('digits:', [len(str(x)) for x in (t1, t2, T, C, N)], '| nd2N / lcm(t1,t2,t1-1,t2-1,T,C,condN) =', N // math.lcm(t1, t2, t1-1, t2-1, T, C, condN))
sys.exit(bad)
