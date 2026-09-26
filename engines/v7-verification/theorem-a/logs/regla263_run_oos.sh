#!/bin/zsh
# out-of-sample vdim gates of the Gamma-law (cells NOT gated by the Fable)
q=$1; n=$2; shift 2
for mu in "$@"; do
  f=regla263_sing/o_${q}_${n}_${mu}.sing
  python3 herramientas_grepy/regla263_gamma.py vdim $q $n $mu > $f
  /usr/bin/time -p Singular -q $f 2>&1 | grep -E 'mu=|real'
done
