import sys, runpy, numpy as np
sys.argv=['x','300','150','40']
g = runpy.run_path('thms/sl2_gram.py')
R=g['R']; w,V=np.linalg.eigh(R)
for i in np.argsort(-w)[:25]:
    v=V[:,i]; top=np.argsort(-np.abs(v))[:4]+1
    print(round(w[i],6), 'main indices', top, np.round(np.abs(v[top-1]),3))
print('max |r(m,n)| over n!=m, m=1..6:', [float(np.round(np.abs(np.delete(R[m-1],m-1)).max(),8)) for m in range(1,7)])
