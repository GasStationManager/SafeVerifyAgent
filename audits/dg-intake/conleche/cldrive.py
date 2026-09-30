import json,os,subprocess,time,sys
S='/tmp/claude-0/-home-user/69126eca-8d7d-5969-ab6e-745654c8c3a5/scratchpad/dgbuild/'
O='/tmp/claude-0/-home-user/69126eca-8d7d-5969-ab6e-745654c8c3a5/scratchpad/conleche/'
E='/tmp/claude-0/-home-user/69126eca-8d7d-5969-ab6e-745654c8c3a5/scratchpad/lean4export/.lake/build/bin/lean4export'
C='/home/user/con-leche/.lake/build/bin/con-leche'
root='/home/user/differential-geometry'
env=dict(os.environ); env['PATH']=os.path.expanduser('~/.elan/bin')+':'+env['PATH']
jobs=json.load(open(S+'conleche_jobs.json'))
done={json.loads(l)['module'] for l in open(O+'results.jsonl')} if os.path.exists(O+'results.jsonl') else set()
for g in jobs:
    m=g['module']
    if m in done: continue
    nd=O+m+'.ndjson'
    t=time.time()
    with open(nd,'w') as f:
        r=subprocess.run(['lake','env',E,m,'--',*g['decls']],cwd=root,env=env,stdout=f,stderr=subprocess.PIPE,text=True)
    texp=time.time()-t; size=os.path.getsize(nd)
    rec=dict(module=m,decls=g['decls'],titles=g['titles'],closure=g['closure'],export_s=round(texp),export_rc=r.returncode,export_err=r.stderr[-800:],ndjson_bytes=size)
    if r.returncode==0 and size>0:
        rec['records']=sum(1 for _ in open(nd,'rb'))
        for mode in ('--verified',):
            t=time.time()
            c=subprocess.run([C,mode,nd],capture_output=True,text=True)
            rec['conleche_mode']=mode; rec['conleche_s']=round(time.time()-t,1); rec['conleche_rc']=c.returncode
            rec['conleche_out']=(c.stdout.strip()+' '+c.stderr.strip())[-600:]
        # axioms declared in the stream
        ax=[]
        for line in open(nd,encoding='utf-8',errors='replace'):
            if '"axiom"' in line[:60] or '"kind":"axiom"' in line: ax.append(line.strip()[:200])
        rec['axiom_records']=ax[:20]
        os.remove(nd) if size>2e9 else None
    with open(O+'results.jsonl','a') as f: f.write(json.dumps(rec)+'\n')
    print('DONE',m,rec.get('conleche_out','')[:120],flush=True)
print('ALL_DONE')
