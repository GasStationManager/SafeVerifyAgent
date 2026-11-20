import sys, os, re, collections
root = sys.argv[1]
imp = re.compile(r'^\s*(?:public\s+|private\s+|meta\s+)*import\s+(?:all\s+)?(\S+)', re.M)
def path(m): return os.path.join(root, *m.split('.')) + '.lean'
seen = {}; missing = collections.defaultdict(list); stack = ['Main']
ext = collections.Counter()
while stack:
    m = stack.pop()
    if m in seen: continue
    p = path(m)
    try: src = open(p, encoding='utf-8').read()
    except FileNotFoundError:
        seen[m] = None; continue
    # strip block comments crudely
    deps = imp.findall(src)
    seen[m] = deps
    for d in deps:
        top = d.split('.')[0]
        if top in ('Mathlib','Lean','Batteries','Std','Init','Aesop','Qq','Plausible','ProofWidgets','ImportGraph','LeanSearchClient','Cli'):
            ext[d if top!='Mathlib' else 'Mathlib.*'] += 1; continue
        if not os.path.exists(path(d)): missing[d].append(m)
        stack.append(d)
inproj = [m for m,v in seen.items() if v is not None]
print('closure modules:', len(inproj))
print('missing imports:', len(missing), list(missing.items())[:10])
print('external:', ext.most_common(20))
c = collections.Counter(m.split('.')[0] for m in inproj); print(c)
open(sys.argv[2],'w').write('\n'.join(sorted(inproj)))
allf = sum(len(fs) for _,_,fs in os.walk(root))
print('all files', allf)
