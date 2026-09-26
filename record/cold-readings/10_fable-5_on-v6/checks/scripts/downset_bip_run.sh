#!/bin/zsh
# downset_bip_run.sh <logfile> <prediction-file> <command...>
# Runs one command under /usr/bin/time -l and assembles the log:
#   top: exact command, wall time, peak memory (maximum resident set size)
#   then: the prediction written BEFORE the run, then the program output, then the raw time -l block.
LOG=$1; PRED=$2; shift 2
OUT=$(mktemp); TIMEF=$(mktemp)
/usr/bin/time -l "$@" > "$OUT" 2> "$TIMEF"
STATUS=$?
WALL=$(grep ' real ' "$TIMEF" | awk '{print $1}')
MRSS=$(grep 'maximum resident set size' "$TIMEF" | awk '{print $1}')
{
  echo "=== RUN ==="
  echo "command: $*"
  echo "cwd: $(pwd)"
  echo "date: $(date)"
  echo "exit status: $STATUS"
  echo "wall time (/usr/bin/time -l, real): $WALL s"
  echo "peak memory (maximum resident set size): $MRSS bytes = $(( MRSS / 1048576 )) MB"
  echo "=== PREDICTION (written before the run) ==="
  cat "$PRED"
  echo "=== OUTPUT ==="
  cat "$OUT"
  echo "=== /usr/bin/time -l (raw) ==="
  cat "$TIMEF"
} > "$LOG"
rm -f "$OUT" "$TIMEF"
echo "log written: $LOG (exit $STATUS, wall $WALL s, peak $(( MRSS / 1048576 )) MB)"
exit $STATUS
