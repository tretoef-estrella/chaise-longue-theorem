#!/bin/zsh
q=$1; n1=$2; shift 2
for mu in "$@"; do
  f=regla263_sing/r_${q}_${n1}_${mu}.sing
  python3 herramientas_grepy/regla263_gamma.py rows $q $n1 $mu > $f
  /usr/bin/time -p Singular -q $f 2>&1 | grep -E 'PARENT|bad=[1-9]|real'
done
