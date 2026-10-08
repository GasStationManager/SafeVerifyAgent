#!/usr/bin/env python3
"""Compare definition bodies between two lean4export NDJSON files (format 3.x) up to
alpha-equivalence (binder names ignored; binder info compared separately).
usage: holediff.py challenge.ndjson solution.ndjson NAME..."""
import json, sys
def load(path):
    names, levels, exprs, consts = {}, {}, {}, {}
    with open(path, 'rb') as f:
        for raw in f:
            try: o = json.loads(raw)
            except Exception: continue
            if 'in' in o:
                i = o['in']
                if 'str' in o: names[i] = ('str', o['str']['pre'], o['str']['str'])
                elif 'num' in o: names[i] = ('num', o['num']['pre'], o['num']['i'])
            elif 'il' in o:
                i = o['il']; k = [k for k in o if k != 'il'][0]; levels[i] = (k, o[k])
            elif 'ie' in o:
                i = o['ie']; k = [k for k in o if k != 'ie'][0]; exprs[i] = (k, o[k])
            else:
                for kind in ('def','thm','axiom','opaque','quot','ind','ctor','rec'):
                    if kind in o: consts[(kind, o[kind]['name'])] = o[kind]; break
    return names, levels, exprs, consts
def nm(names, i, cache={}):
    if i == 0: return ''
    k, pre, s = names[i]
    p = nm(names, pre); return (p + '.' if p else '') + str(s)
def lv(levels, i):
    if i == 0: return 'z'
    k, v = levels[i]
    if k == 'succ': return 's(' + lv(levels, v) + ')'
    if k in ('max','imax'): return k + '(' + lv(levels, v[0]) + ',' + lv(levels, v[1]) + ')'
    if k == 'param': return 'p:' + str(v)
    return k + str(v)
def ex(E, names, levels, i, memo, binfo):
    if i in memo: return memo[i]
    k, v = E[i]
    if k == 'bvar': r = '#' + str(v)
    elif k == 'sort': r = 'S(' + lv(levels, v) + ')'
    elif k == 'const': r = 'C(' + nm(names, v['name']) + '{' + ','.join(lv(levels,u) for u in v['us']) + '})'
    elif k == 'app': r = '(' + ex(E,names,levels,v['fn'],memo,binfo) + ' ' + ex(E,names,levels,v['arg'],memo,binfo) + ')'
    elif k in ('lam','pi','forallE'):
        binfo.append(v.get('binderInfo'))
        r = ('λ' if k=='lam' else 'Π') + '[' + ex(E,names,levels,v['type'],memo,binfo) + ']' + ex(E,names,levels,v['body'],memo,binfo)
    elif k in ('let','letE'): r = 'let[' + ex(E,names,levels,v['type'],memo,binfo) + ':=' + ex(E,names,levels,v['value'],memo,binfo) + ']' + ex(E,names,levels,v['body'],memo,binfo)
    elif k in ('lit','natVal','strVal'): r = 'L(' + json.dumps(v, sort_keys=True) + ')'
    elif k == 'proj': r = 'proj(' + nm(names, v['typeName']) + ',' + str(v['idx']) + ',' + ex(E,names,levels,v['struct'],memo,binfo) + ')'
    elif k == 'mdata': r = ex(E,names,levels,v['expr'],memo,binfo)
    else: r = k + json.dumps(v, sort_keys=True)
    memo[i] = r; return r
def find(consts, names, target):
    for (kind, ni), c in consts.items():
        if nm(names, ni) == target: return kind, c
    return None, None
def main():
    ch, so, targets = sys.argv[1], sys.argv[2], sys.argv[3:]
    C = load(ch); S = load(so)
    for t in targets:
        kc, cc = find(C[3], C[0], t); ks, cs = find(S[3], S[0], t)
        if cc is None or cs is None: print(f'{t}: MISSING challenge={kc} solution={ks}'); continue
        out = [f'{t}: kind {kc}/{ks}']
        for field in ('type', 'value'):
            if field not in cc or field not in cs: out.append(f'  {field}: absent ({field in cc}/{field in cs})'); continue
            bc, bs = [], []
            a = ex(C[2], C[0], C[1], cc[field], {}, bc); b = ex(S[2], S[0], S[1], cs[field], {}, bs)
            same = a == b
            out.append(f'  {field}: {"ALPHA-EQUAL" if same else "DIFFERENT"} ({len(a)} vs {len(b)} chars; binderInfo {"equal" if bc==bs else "differ"})')
            if not same:
                # first divergence
                k = next((i for i in range(min(len(a),len(b))) if a[i]!=b[i]), min(len(a),len(b)))
                out.append('    challenge: ...' + a[max(0,k-120):k+200]); out.append('    solution : ...' + b[max(0,k-120):k+200])
        for f in ('levelParams','safety','hints'):
            if cc.get(f) != cs.get(f): out.append(f'  {f}: {cc.get(f)} vs {cs.get(f)}')
        print('\n'.join(out))
main()
