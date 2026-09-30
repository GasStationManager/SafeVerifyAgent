import re,os,json,importlib.util
S='/tmp/claude-0/-home-user/69126eca-8d7d-5969-ab6e-745654c8c3a5/scratchpad/dgbuild/'
spec=importlib.util.spec_from_file_location('mk',S+'mksetup.py'); mk=importlib.util.module_from_spec(spec); spec.loader.exec_module(mk)
root='/home/user/differential-geometry'
def ol(m): return os.path.join(root,'.lake/build/lib/lean',*m.split('.'))+'.olean'
DECL=re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable |scoped |local )*(theorem|lemma|def|instance|structure)\s+([A-Za-z0-9_.'!?₀-ₜ¹²³]+)")
def decl_at(path,line):
    L=open(path,encoding='utf-8').read().split('\n')
    for i in range(line-1,min(line+40,len(L))):
        m=DECL.match(L[i])
        if m:
            ns=[]
            for j in range(i):
                t=L[j]
                mm=re.match(r'^namespace\s+([A-Za-z0-9_.]+)',t)
                if mm: ns.append(mm.group(1))
                me=re.match(r'^end\s+([A-Za-z0-9_.]+)',t)
                if me and ns and me.group(1)==ns[-1]: ns.pop()
            return '.'.join(ns+[m.group(2)]) if ns else m.group(2), m.group(1)
    return None,None
targets=[]
for m in re.finditer(r'\[([^\]]+)\]\((DifferentialGeometry/[^)#]+\.lean)#L(\d+)\)',open('README.md').read()):
    title,path,line=m.group(1),m.group(2),int(m.group(3))
    name,kind=decl_at(path,line)
    targets.append(dict(title=title,module=path[:-5].replace('/','.'),decl=name,kind=kind,line=line,source='README'))
picks=[('pinching delta threshold','NormalizedInsertionPinching',134),('pinching through surgery','PinchingThroughSurgery',17),
 ('surgery step (public wrapper)','UniformDebitSurgeryStepOfFineCutNeckSupplyStrong',21),('invariance of domain (vendored)','InvarianceOfDomain',464),
 ('Brouwer instance (native)','Brouwer',30),('no retraction','NoRetraction',14),('cut-cap reversal is connected sum','CutCapPoincareStandard',15),
 ('trivial space form is S3','SphericalSpaceFormTrivial',14),('Van Kampen connected sum','FiniteConnectedSumFreeProduct',277),
 ('Section 34 cell diagram','Section34Terminal',19),('Moise 34.1','Moise341Producer',21),('extinction threshold','ScalarThreshold',11),
 ('event count bound','HistoryEventVolumeBound',27),('width decay on a slab','ActualWidth',428),('simple connectivity through surgery','ChildSimplyConnected',35)]
allfiles={}
for dp,dn,fn in os.walk(root+'/DifferentialGeometry'):
    for f in fn:
        if f.endswith('.lean'): allfiles.setdefault(f[:-5],[]).append(os.path.join(dp,f))
for title,base,line in picks:
    hits=allfiles.get(base,[])
    if base=='Brouwer': hits=[h for h in hits if 'FixedPoint' in h]
    if base=='InvarianceOfDomain': hits=[h for h in hits if 'ClassificationOfSurfaces' in h]
    if not hits: targets.append(dict(title=title,module=base,decl=None,kind='NOTFOUND',line=line,source='audit')); continue
    p=hits[0]; mod=os.path.relpath(p,root)[:-5].replace('/','.')
    name,kind=decl_at(p,line); targets.append(dict(title=title,module=mod,decl=name,kind=kind,line=line,source='audit'))
for t in targets:
    m=t['module']; loc=mk.locate(m)
    if not loc: t['built']=False; t['closure']=0; continue
    seen={}; stack=[m]
    while stack:
        x=stack.pop()
        if x in seen: continue
        l=mk.locate(x); seen[x]=l
        if l: stack+=[i for i in mk.imports_of(l[0]) if i not in seen]
    dg=[x for x in seen if x.startswith('DifferentialGeometry')]
    t['closure']=len(seen); t['built']=all(os.path.exists(ol(x)) for x in dg)
json.dump(targets,open(S+'conleche_targets.json','w'),indent=1)
for t in targets: print(('OK  ' if t['built'] else 'NO  ')+f"{t['closure']:6d} {(t['kind'] or '-'):9s} {t['decl']}  [{t['title'][:38]}]")
