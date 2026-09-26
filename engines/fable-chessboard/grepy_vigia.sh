#!/bin/zsh
# grepy_vigia.sh — the auditor's watchdog (copy of the corpus vigia.sh, header in English), 2026-09-23.
# CAPS OF THE TURN, DO NOT MOVE: 1.2 GB of RSS (the whole process tree, sampled every 0.2 s) and 600 s.
# Usage:  zsh grepy_vigia.sh LOGFILE 'the whole command in quotes'      <- the LOG is the FIRST argument
#   e.g.  zsh grepy_vigia.sh r1.log '/opt/homebrew/bin/M2 --script r1.m2'
# The LAST line of the LOG always says how it ended: VIGIA-FIN-OK / VIGIA-MATADO-MEMORIA / VIGIA-MATADO-TIEMPO.
LOG=$1; shift
TOPE_KB=1258291; TOPE_S=600
zsh -c "$*" > "$LOG" 2>&1 &
P=$!; T0=$SECONDS; PICO=0
arbol() { local p; for p in "$@"; do print $p; arbol $(pgrep -P $p); done }
while kill -0 $P 2>/dev/null; do
  R=0; for q in $(arbol $P); do r=$(ps -o rss= -p $q 2>/dev/null); R=$(( R + ${r:-0} )); done
  (( R > PICO )) && PICO=$R
  if (( R > TOPE_KB )); then kill -9 $(arbol $P) 2>/dev/null; print "VIGIA-MATADO-MEMORIA rss_kb=$R t=$((SECONDS-T0))s" >> "$LOG"; exit 2; fi
  if (( SECONDS - T0 > TOPE_S )); then kill -9 $(arbol $P) 2>/dev/null; print "VIGIA-MATADO-TIEMPO pico_kb=$PICO t=$((SECONDS-T0))s" >> "$LOG"; exit 3; fi
  sleep 0.2
done
wait $P; E=$?
print "VIGIA-FIN-OK exit=$E pico_kb=$PICO t=$((SECONDS-T0))s" >> "$LOG"
