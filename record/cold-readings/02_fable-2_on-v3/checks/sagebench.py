import time
from sage.all import *
t=time.time()
M=random_matrix(GF(3),6000,3000)
print('build',time.time()-t); t=time.time()
print(M.rank()); print('dense rank time',time.time()-t)
t=time.time()
S=random_matrix(GF(3),20000,2000,density=0.005,sparse=True)
print('sparse build',time.time()-t); t=time.time()
print(S.rank()); print('sparse rank time',time.time()-t)
