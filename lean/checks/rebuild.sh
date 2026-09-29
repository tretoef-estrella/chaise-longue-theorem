#!/bin/zsh
cd /Users/rafa/Desktop/ARBOLYAML/ARISTOTLE_LEAN/proyecto_lean/output-final_aristotle
LOG=../clean_rebuild_2026-09-29.log
mv .lake/build .lake/build_bak_2026-09-29 || exit 1
echo "START $(date '+%F %T')" > $LOG
for m in $(cat /private/tmp/claude-501/-Users-rafa-Desktop-ARBOLYAML/2907fe98-9fc7-43a5-9931-a69c5909a49e/scratchpad/order.txt); do
  s=$(date +%s)
  /usr/bin/time -l lake build $m > /tmp/claude-501/rb_one.log 2>&1
  rc=$?
  e=$(date +%s)
  pk=$(grep "peak memory" /tmp/claude-501/rb_one.log | awk '{print $1}')
  echo "$m rc=$rc sec=$((e-s)) lakepeak=$pk" >> $LOG
  if [ $rc -ne 0 ]; then cat /tmp/claude-501/rb_one.log >> $LOG; echo "FAILED" >> $LOG; exit 1; fi
done
echo "END $(date '+%F %T')" >> $LOG
echo "FIN-OK" >> $LOG
