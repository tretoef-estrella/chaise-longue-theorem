#!/bin/zsh
# clean_rebuild_pares.sh — Grepy Mandalay, 3 Oct 2026.
# Clean rebuild of the WHOLE Chaise Longue Lean project (odd and even degrees), as in certificate v1 §8:
# the project's own build directory is moved aside (Mathlib untouched) and every module is rebuilt
# one at a time, in topological order (orden_modulos.txt), each with its own `lake build` under the
# watchdog (Lean cap of Rafa's OK of 30 Sep: 4.5 GB real footprint, 900 s per module).
# Modules marked '#' in orden_modulos.txt are not built (they exceed the cap; declared in the certificate).
# Estimate written before launching: ~233 modules x ~70 s = ~4.5 h; peak ~2.4 GB (largest earlier build).
P=/Users/rafa/Desktop/ARBOLYAML/ARISTOTLE_LEAN/proyecto_lean/output-final_aristotle
D=/Users/rafa/Desktop/ARBOLYAML/ARISTOTLE_LEAN/CERTIFICADO_PARES
V=/Users/rafa/Desktop/ARBOLYAML/corpus4/herramientas_grepy/vigia.sh
LOG=$D/clean_rebuild_2026-10-03.log
mkdir -p $D/cr_logs
cd $P || exit 1
if [ -e .lake/build_pre_clean_2026-10-03 ]; then echo "backup exists, stop" >> $LOG; exit 1; fi
mv .lake/build .lake/build_pre_clean_2026-10-03 || exit 1
echo "START $(date '+%Y-%m-%d %H:%M:%S')" >> $LOG
n=0; fails=0
while read mod; do
  case "$mod" in '#'*) echo "SKIPPED ${mod#\#}" >> $LOG; continue;; esac
  n=$((n+1)); s=$(date +%s)
  L=$D/cr_logs/$mod.log
  TOPE_KB=4718592 TOPE_S=900 zsh $V $L "lake build $mod"
  last=$(tail -n 1 $L)
  echo "$mod $last wall=$(( $(date +%s) - s ))s" >> $LOG
  case "$last" in *'VIGIA-FIN-OK exit=0'*) ;; *) fails=$((fails+1));; esac
done < $D/orden_modulos.txt
echo "END $(date '+%Y-%m-%d %H:%M:%S') modules=$n fails=$fails" >> $LOG
[ $fails -eq 0 ] && echo FIN-OK >> $LOG || echo FIN-FAIL >> $LOG
