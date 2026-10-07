import numpy as np, itertools
M=np.array([
 [[6,0,0,0],[0,6,0,0],[0,0,6,0],[0,0,0,6],[0,0,0,0],[0,0,0,0]],
 [[-12,0,0,0],[0,-6,0,0],[0,0,6,0],[0,0,0,12],[-6,0,6,6],[-6,-6,6,0]],
 [[0,6,-2,0],[6,6,0,2],[-2,0,10,0],[0,2,0,24],[0,0,0,6],[0,-6,6,-6]],
 [[0,0,-4,-3],[0,-2,-3,-4],[-4,-3,11,6],[-3,-4,6,25],[6,6,0,0],[0,-6,6,6]]],dtype=complex)
print("sym (7.4):",all(np.allclose(M[i].T@M[j],M[j].T@M[i]) for i in range(4) for j in range(4)))
print("M0^T M0 = 36I:",np.allclose(M[0].T@M[0],36*np.eye(4)))
def E(n,i,j):
    X=np.zeros((n,n),complex);X[i,j]=1;return X
def L(A): return sum(A[i,j]*(M[i].T@M[j]) for i in range(4) for j in range(4))
def tensorMap(F,G,X,a,c):  # X indexed (a,c) row-major
    X4=X.reshape(a,c,a,c)
    return sum(np.kron(F(X4[:,i,:,j]),G(E(c,i,j))) for i in range(c) for j in range(c))
sp=[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)]
ep=[(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
U=np.zeros((16,10),complex);V=np.zeros((16,6),complex)
for a,(p,q) in enumerate(sp):
    if p==q: U[4*p+p,a]=1
    else: U[4*p+q,a]=U[4*q+p,a]=1/np.sqrt(2)
for a,(p,q) in enumerate(ep):
    V[4*p+q,a]=1/np.sqrt(2); V[4*q+p,a]=-1/np.sqrt(2)
K=np.array([[0,0,0,0,0,1],[0,0,0,0,-1,0],[0,0,0,1,0,0],[0,0,1,0,0,0],[0,-1,0,0,0,0],[1,0,0,0,0,0]],complex)
Ef=np.zeros((10,6),complex);Ef[:6,:6]=np.eye(6)
S=lambda A: V.conj().T@tensorMap(L,L,U@A@U.conj().T,4,4)@V
R=lambda A: K@S(A).T@K.conj().T
def hsAdj(F,n_in,Y):
    return np.array([[np.sum(np.conj(F(E(n_in,i,j)))*Y) for j in range(n_in)] for i in range(n_in)])
phi1=lambda A: Ef@S(A.T)@Ef.conj().T
phi2=lambda B: hsAdj(R,10,Ef.conj().T@B@Ef)
Z=np.zeros((100,100),complex)
for i in range(10):
  for j in range(10):
    Z[10*i:10*i+10,10*j:10*j+10]=phi2(phi1(E(10,i,j)))
w=np.linalg.eigvalsh((Z+Z.conj().T)/2)
print("hermitian",np.allclose(Z,Z.conj().T),"min eig",w.min(),"max",w.max(),"rank",np.sum(w>1e-6*w.max()))
print("Z[00,00]",Z[0,0].real,"expect",6*36**4)
print("trace",np.trace(Z).real)
# partial transpose PSD check (state is PPT)
Z4=Z.reshape(10,10,10,10); ZT=Z4.transpose(0,3,2,1).reshape(100,100)
print("PT min eig",np.linalg.eigvalsh(ZT).min())
