# run12.sh Q "mu:n mu:n ..." [opts]  — one watchdog run per cell, summary to run12_Q.sum
Q=$1; CELLS=$2; shift 2; OPTS="$*"
for c in ${=CELLS}; do mu=${c%%:*}; n=${c##*:}; tag=c12_${mu//,/}_${n}_$Q
  python3 cert12.py $mu $n $Q ${=OPTS} > $tag.sing
  zsh grepy_vigia.sh $tag.log "Singular -q $tag.sing"
  W=$(python3 -c "from fibre import W; print(W(tuple(int(x) for x in '$mu'.split(',')),$n,$Q))")
  print "== $mu n=$n q=$Q |W|=$W" ; grep -E "RESULT|NEW beyond|LAW|VIGIA" $tag.log
done
