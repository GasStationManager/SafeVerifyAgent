import re, sys, json, collections
src = open('/home/user/ten-proofs/GapCVP.lean').read().split('\n')
decl_re = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial)\s+)*(theorem|lemma|def|abbrev|structure|instance|inductive|class)(?:\s+|$)(?:\(priority[^)]*\)\s*)?([^\s:({\[]+)?')
stack=[]  # entries ('ns',name) or ('sec',name)
decls=[]  # (fullname, kind, start)
cur=None
for i,l in enumerate(src,1):
    m=re.match(r'^namespace\s+(\S+)',l)
    if m: stack.append(('ns',m.group(1))); continue
    m=re.match(r'^(noncomputable\s+)?section\b\s*(\S*)',l)
    if m: stack.append(('sec',m.group(2))); continue
    m=re.match(r'^end\b\s*(\S*)',l)
    if m and not l.startswith('end ') or (m and True):
        if m:
            if stack: stack.pop()
            continue
    # declarations may start after a line '@[...]' alone or 'noncomputable def\n name'
    m=decl_re.match(l)
    if m and m.group(1):
        name=m.group(2)
        if name is None or name in ('where',):
            # name on next line
            nxt=src[i].strip().split()[0] if i<len(src) else ''
            name=nxt
        ns='.'.join(n for k,n in stack if k=='ns' and n)
        full=(ns+'.'+name) if ns else name
        if name.startswith('_root_.'): full=name[7:]
        decls.append([full,m.group(1),i])
# structure fields / ctor names not tracked
ends=[d[2] for d in decls[1:]]+[len(src)+1]
for d,e in zip(decls,ends): d.append(e-1)
byshort=collections.defaultdict(list)
for idx,d in enumerate(decls):
    parts=d[0].split('.')
    for k in range(len(parts)):
        byshort['.'.join(parts[k:])].append(idx)
tok=re.compile(r"[A-Za-z_][A-Za-z0-9_'!?₀-₉]*(?:\.[A-Za-z_][A-Za-z0-9_'!?₀-₉]*)*")
refs={}
for idx,d in enumerate(decls):
    body='\n'.join(src[d[2]-1:d[3]])
    s=set()
    for t in set(tok.findall(body)):
        parts=t.split('.')
        for k in range(len(parts)):
            key='.'.join(parts[k:])
            if key in byshort:
                for j in byshort[key]:
                    if j!=idx: s.add(j)
                break
    refs[idx]=s
def cone(rootname):
    roots=[i for i,d in enumerate(decls) if d[0]==rootname]
    seen=set(roots); st=list(roots)
    while st:
        x=st.pop()
        for y in refs[x]:
            if y not in seen: seen.add(y); st.append(y)
    return seen
if __name__=='__main__':
    root=sys.argv[1]
    c=cone(root)
    kinds=collections.Counter(decls[i][1] for i in c)
    lines=sum(decls[i][3]-decls[i][2]+1 for i in c)
    print(len(decls),'decls total;',len(c),'in cone',dict(kinds),'lines',lines)
    if len(sys.argv)>2:
        json.dump(sorted([decls[i][:4] for i in c],key=lambda d:d[2]),open(sys.argv[2],'w'))
