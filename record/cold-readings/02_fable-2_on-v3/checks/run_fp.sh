#!/bin/zsh
# Section-6 experiment: the paper's (S), transposed verbatim to F_p, q = p^v, p = 5, 7.
# PREDICTIONS (Q_k(q) from the generating function, written before running):
#  F_5: (1,5)=36 (2,5)=400 (3,5)=4900 (1,25)=1656 (2,25)=182400 (1,125)=45756
#  F_7: (1,7)=90 (2,7)=1860 (1,49)=6768
# Known by other means: (1,q) all q [De14]; (2,5),(2,7),(3,5) by [DS] computer. NEW: (1,25),(2,25),(1,125),(1,49).
# Estimates: (2,25): 24^5 = 8.0M monomials, like (2,27): ~20 s, <1 GB. (1,125): 124^3 = 1.9M: ~1 min. Others trivial.
python3 symdualp.py 1 3 3
for c in "1 5 5" "2 5 5" "3 5 5" "1 7 7" "2 7 7" "1 25 5" "1 49 7" "1 125 5" "2 25 5"; do
  /usr/bin/time -l python3 symdualp.py ${=c} 2>&1 | egrep "FIELD|real|maximum resident" | cut -c1-140
done
