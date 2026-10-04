#!/usr/bin/env python3
"""STEP 5b — the first non-prime-power cell, (m,k) = (15,1), from the Lean formula of psiP.
Expected: dim_Fp of the ideal = Qk 1 15 = 546 for p = 3, 5 (the primes dividing m), 2, 7 and a large
prime; so dim of the quotient = 3375 - 546 = 2829 for every p (=> Z-quotient torsion-free at 3 and 5,
the only primes that can matter by [DS, Cor. 1.5], which is NOT formalized and is used here only to
choose primes). Time estimate: 3-6 min; memory: ~0.3-0.7 GB (10125 x 3375 int64 matrix + temporaries).
"""
import sys, time, os
sys.argv = ['x']
src = open(os.path.join(os.path.dirname(__file__), 's5_math.py')).read()
# reuse only the function definitions of s5_math.py (no top-level checks)
defs = {}
import itertools, numpy as np
from math import factorial
for name in ('def Qk', 'def matchings', 'def psi_poly', 'def ideal_matrix', 'def rank_mod_p'):
    i = src.index(name); j = src.find('\ndef ', i + 1); j2 = src.find('\nprint(', i + 1)
    j = min(x for x in (j, j2) if x > 0)
    exec(src[i:j], globals())
t0 = time.time(); A, n = ideal_matrix(15, 1); print('matrix', A.shape, f'{time.time()-t0:.1f}s', flush=True)
q = Qk(1, 15); print('Qk 1 15 =', q)
for p in (3, 5, 2, 7, 2147483629):
    t0 = time.time(); r = rank_mod_p(A, p)
    print(f'p={p}: dim ideal = {r} ({"ok" if r == q else "FAIL"}), dim quotient = {n - r}  [{time.time()-t0:.1f}s]', flush=True)
