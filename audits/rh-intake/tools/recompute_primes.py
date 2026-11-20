"""Independent recomputation of the arithmetic facts in the artifact's prime certificates.
Reads source only. Usage: recompute_primes.py <src-root>"""
import sys, os, re, random
root = sys.argv[1]
def is_prime(n):
    if n < 2: return False
    small = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71]
    for p in small:
        if n % p == 0: return n == p
    d, s = n-1, 0
    while d % 2 == 0: d//=2; s+=1
    rnd = random.Random(1)
    for a in small + [rnd.randrange(2, n-1) for _ in range(40)]:
        x = pow(a, d, n)
        if x in (1, n-1): continue
        for _ in range(s-1):
            x = x*x % n
            if x == n-1: break
        else: return False
    return True
def ev(e):  # evaluate a closed Nat expression with truncated subtraction and floor division
    e = e.replace('^','**').replace('/','//')
    if not re.fullmatch(r'[0-9()+\-*/ ]+', e): raise ValueError(e)
    return eval(e)
pow_stmt = re.compile(r'theorem\s+(\S+)\s*:\s*(\d+)\s*\^\s*(\(.*?\)|\d+)\s*%\s*(\d+)\s*=\s*(\d+)\s*:=')
base = re.compile(r'have h : (\d+) \^ (\d+) % (\d+) = (\d+) := by decide')
step = re.compile(r"pow_mod_of_two_pow_window \(e' := (.+?)\) \(s := (\d+)\) (\d+) (\d+) h")
prime = re.compile(r'(?:Nat\.Prime\s+\(?(\d{4,})\b|\(?(\d{4,})\s*:\s*ℕ\)\.Prime|\b(\d{4,})\.Prime)')
tot = dict(pow_ok=0, pow_bad=0, step_ok=0, step_bad=0, prime_ok=0, prime_bad=0)
seen_primes = {}
for dp, _, fs in os.walk(root):
    for f in fs:
        if not f.endswith('.lean'): continue
        p = os.path.join(dp, f); src = open(p, encoding='utf-8').read()
        if not re.search(r'\d{4,}', src): continue
        for m in prime.finditer(src):
            n = int(next(g for g in m.groups() if g))
            seen_primes.setdefault(n, []).append(os.path.relpath(p, root))
        if 'pow_mod_of_two_pow_window' not in src and not pow_stmt.search(src): continue
        lines = src.split('\n'); cur = None
        for ln in lines:
            m = pow_stmt.search(ln)
            if m:
                a, E, n, s = int(m[2]), ev(m[3]), int(m[4]), int(m[5])
                ok = pow(a, E, n) == s
                tot['pow_ok' if ok else 'pow_bad'] += 1
                if not ok: print('BAD POW', p, m[1])
                cur = dict(a=a, n=n, E=E, s=s, name=m[1]); continue
            m = base.search(ln)
            if m and cur:
                a, e, n, r = map(int, m.groups())
                ok = (a, n) == (cur['a'], cur['n']) and pow(a, e, n) == r
                tot['step_ok' if ok else 'step_bad'] += 1
                if not ok: print('BAD BASE', p, cur['name'])
                cur.update(e=e, r=r); continue
            m = step.search(ln)
            if m and cur and 'e' in cur:
                e2, s2, k, w = ev(m[1]), int(m[2]), int(m[3]), int(m[4])
                ok = (2**k * cur['e'] + w == e2) and (cur['r']**(2**k) * cur['a']**w % cur['n'] == s2) and pow(cur['a'], e2, cur['n']) == s2
                tot['step_ok' if ok else 'step_bad'] += 1
                if not ok: print('BAD STEP', p, cur['name'], m[1][:30])
                cur.update(e=e2, r=s2)
for n, where in sorted(seen_primes.items()):
    ok = is_prime(n); tot['prime_ok' if ok else 'prime_bad'] += 1
    print(('prime    ' if ok else 'COMPOSITE'), n if n < 10**20 else f'{str(n)[:12]}…({len(str(n))} digits)', sorted(set(where))[0].split('/')[-1], len(where))
print(tot)
