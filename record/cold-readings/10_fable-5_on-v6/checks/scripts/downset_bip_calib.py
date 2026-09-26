#!/usr/bin/env python3
"""downset_bip_calib.py -- calibrate the time model of the engine on random matrices
(no mathematics of the paper is involved).  Prints model-flops/second for the Echelon class."""
import sys
import time

import numpy as np

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from downset_bip_engine import Echelon  # noqa

rng = np.random.default_rng(0)
print("two-term model: t = mm/RATE_MM + el/RATE_EL, mm = rows*(n/2)*n, el = 3*(n/2)*batch*n (batch=128)")
for (p, m, n) in ((5, 10506, 1751), (3, 8856, 1107), (7, 7255, 1451), (11, 3564, 891), (19, 2660, 1330),
                  (3, 2000, 1107), (19, 300, 1330)):
    M = rng.integers(0, p, (m, n)).astype(np.float32)
    t = time.time()
    E = Echelon(p, n)
    E.add(M)
    dt = time.time() - t
    mm = m * (n / 2) * n
    el = 3 * (n / 2) * min(128, m) * n
    print("p=%2d  %6d x %5d  rank %5d  %.2fs  | mm %.2e el %.2e | if only mm: %.2e/s ; if only el: %.2e/s" % (
        p, m, n, E.rank, dt, mm, el, mm / dt, el / dt))
