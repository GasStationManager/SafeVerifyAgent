import sys, os, re, collections, random, json
root = sys.argv[1]
imp = re.compile(r'^\s*import\s+(\S+)', re.M)
EXT=('Mathlib','Lean','Batteries','Std','Init')
mods={}
for dp,_,fs in os.walk(root):
    for f in fs:
        if f.endswith('.lean'):
            p=os.path.join(dp,f); m=os.path.relpath(p,root)[:-5].replace('/','.')
            mods[m]=[d for d in imp.findall(open(p,encoding='utf-8').read()) if d.split('.')[0] not in EXT]
# depth (longest chain) via iterative topo
depth={}; 
import sys; sys.setrecursionlimit(10000)
order=[]; state={}
for s in mods:
    if s in state: continue
    st=[(s,iter(mods[s]))]; state[s]=1
    while st:
        n,it=st[-1]
        for d in it:
            if d not in state:
                state[d]=1; st.append((d,iter(mods[d]))); break
            elif state[d]==1: print('CYCLE',n,d)
        else:
            state[n]=2; depth[n]=1+max((depth[d] for d in mods[n]),default=0); order.append(n); st.pop()
print('modules',len(mods),'leaves',sum(1 for m in mods if not mods[m]),'max depth',max(depth.values()), 'depth Main', depth['Main'])
h=collections.Counter(min(depth[m],10) if depth[m]<10 else (depth[m]//100)*100 for m in mods); print(sorted(h.items()))
# closure sizes with bitsets is heavy; do closure size for small-depth modules only via memo sets up to cap
CAP=40
clo={}
for n in order:
    s={n}
    for d in mods[n]:
        c=clo[d]
        if c is None: s=None;break
        s|=c
        if len(s)>CAP: s=None;break
    clo[n]=s
small=[m for m in mods if clo[m] is not None]
print('modules with closure<=%d: %d'%(CAP,len(small)))
random.seed(20261120)
leaves=sorted(m for m in mods if not mods[m])
nonleaf=sorted(m for m in small if mods[m])
json.dump({'leaves':random.sample(leaves,60),'small':random.sample(nonleaf,30),'depth':{m:depth[m] for m in random.sample(sorted(mods),5)}},open(sys.argv[2],'w'),indent=0)
indeg=collections.Counter(d for m in mods for d in mods[m]); print('never imported:',[m for m in mods if indeg[m]==0][:10])
