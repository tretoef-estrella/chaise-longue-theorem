#!/bin/zsh
# PREDICTIONS written before running: (1,27)=1950 (printed, calibration); (1,81)=18960 (NOT printed); (1,243)=174966 (NOT printed).
# Estimate: (1,81): 80^3=512k monomials, <=240 columns per degree, trivial. (1,243): 242^3=14.2M monomials over 724 degrees,
# <= 726 columns per degree, rows <= 44k per degree: rank per degree cheap; building rows in Python ~ 14.2M*3 dict ops ~ minutes.
ulimit -v 1500000
for q in 27 81 243; do /usr/bin/time -l python3 dualform.py 1 $q 2>&1 | egrep "intersection form|maximum resident|real" ; done
