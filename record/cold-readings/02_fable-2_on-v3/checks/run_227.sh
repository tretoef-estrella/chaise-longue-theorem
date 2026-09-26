#!/bin/zsh
# PREDICTION written before the run: (2,27): b_2(26) = dim (D_J)C = Q_2(27) = 234 260.
# ESTIMATE: 26^5 = 11 881 376 monomials over 126 degrees; per degree <= ~283k monomials, ~71k orbit reps under V_4,
# target <= 15*~540 = 8.1k, chi-columns <= ~2.1k; streaming RREF in C ~ r^2 c per (degree,chi) -> a few minutes total; < 1 GB.
/usr/bin/time -l python3 symdual.py 2 27 -v
