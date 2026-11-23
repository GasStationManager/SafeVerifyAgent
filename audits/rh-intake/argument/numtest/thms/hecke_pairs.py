import sys, runpy, numpy as np
sys.argv=['x','600','300','20']
g = runpy.run_path('thms/sl2_gram.py')
R=g['R']; D=g['D']; M=g['M']
rng=np.random.default_rng(1)
# top single pairs in large range
lo=150; idx=np.arange(lo,M); sub=np.abs(R[np.ix_(idx,idx)]); np.fill_diagonal(sub,0)
flat=np.argsort(-sub.ravel())[:8]
print('top pairs (m,n,D r^2):',[(int(idx[i//len(idx)]+1),int(idx[i%len(idx)]+1),round(float(D*sub.ravel()[i]**2),2)) for i in flat])
for p in [2,3]:
  for b in [12,24]:
    rs=[];rg=[]
    for _ in range(300):
      I=rng.choice(np.arange(60,M//p+1),size=b,replace=False)   # indices m (1-based)
      I=I[I%p!=0]
      J=p*I
      rs.append(np.sum(R[np.ix_(I-1,J-1)]**2)/(len(I)**2/D))
      I2=rng.choice(np.arange(60,M+1),size=len(I),replace=False)
      J2=rng.choice(np.setdiff1d(np.arange(60,M+1),I2),size=len(I),replace=False)
      rg.append(np.sum(R[np.ix_(I2-1,J2-1)]**2)/(len(I)**2/D))
    print(f'p={p} b~{b}: Hecke-related blocks (I, pI): mean ratio {np.mean(rs):.3f} max {np.max(rs):.2f} | generic blocks: mean {np.mean(rg):.3f} max {np.max(rg):.2f}')
