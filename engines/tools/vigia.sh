#!/bin/zsh
# vigia.sh — Grepy el Genio, 2026-09-18. GUARDARRAÍL DE RAFA: ningún motor pasa de 1,6 GB ni de 10 min.
# Uso:  zsh corpus4/herramientas_grepy/vigia.sh LOG 'orden entera entre comillas'
# Lanza la orden en segundo plano (stdout+stderr a LOG), suma cada 0,2 s la RSS de TODO el árbol de procesos
# y lo mata si pasa de TOPE_KB (1,2 GB: margen de 400 MB bajo el 1,6 GB de Rafa, porque una asignación rápida sube entre dos muestras) o de TOPE_S (600 s).
# La última línea del LOG dice siempre cómo terminó: VIGIA-FIN-OK / VIGIA-MATADO-MEMORIA / VIGIA-MATADO-TIEMPO.
# v2 (2026-09-18, MISIÓN 24): tope 1,2 GB y muestreo cada 0,2 s. En la v1 (1,5 GB, cada 1 s) dos corridas llegaron a 1,7 GB antes de morir.
LOG=$1; shift
TOPE_KB=${TOPE_KB:-1258291}; TOPE_S=${TOPE_S:-600}
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
