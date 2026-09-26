#!/bin/zsh
# sequential batch under the watchdog (capped_run.sh): one run at a time, one log per run
cd /Users/rafa/Desktop/LECTORES_EN_FRIO/FABLE_5/checks
run() { m=$1; p=$2; mode=$3; Q=$((3*(m-1)*(m-2)));
  ./scripts/capped_run.sh logs/literal_k1_m${m}_p${p}_${mode}.log "dim ideal = Q_1($m) = $Q, quotient $((m*m*m - Q)); est. < 5 min, < 900 MB" python3 scripts/literal_k1.py $m $p $mode; }
run 15 3 all
run 15 5 all
run 21 3 all
run 21 7 all
run 15 3 reduced
run 15 5 reduced
run 21 7 reduced
run 33 3 reduced
run 33 11 reduced
run 35 5 reduced
run 35 7 reduced
run 39 3 reduced
run 39 13 reduced
echo BATCH_DONE
