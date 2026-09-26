#!/bin/zsh
# capped_run.sh LOGFILE "PREDICTION TEXT" command args...
# Runs the command under /usr/bin/time -l, polls its RSS every 0.5 s and KILLS it if RSS > 1150 MB or wall time > 600 s.
# The log gets a header with the command, the prediction, the date, then the output, then the time/memory report.
LOG=$1; shift; PRED=$1; shift
{ echo "# command: $*"; echo "# prediction: $PRED"; echo "# cap: 1150 MB RSS (polled every 0.5 s) and 600 s wall; run date: $(date)"; } > "$LOG"
/usr/bin/time -l "$@" >> "$LOG" 2>&1 &
TPID=$!
sleep 0.3
CPID=$(pgrep -P $TPID | head -1)
[ -z "$CPID" ] && CPID=$TPID
START=$(date +%s); MAXRSS=0; KILLED=""
while kill -0 $TPID 2>/dev/null; do
  RSS=$(ps -o rss= -p $CPID 2>/dev/null | tr -d ' ')
  [ -n "$RSS" ] && [ "$RSS" -gt "$MAXRSS" ] && MAXRSS=$RSS
  NOW=$(date +%s)
  if [ -n "$RSS" ] && [ "$RSS" -gt 1150000 ]; then kill -9 $CPID 2>/dev/null; KILLED="MEMORY ($RSS KB)"; fi
  if [ $((NOW-START)) -gt 600 ]; then kill -9 $CPID 2>/dev/null; KILLED="TIME (>600 s)"; fi
  sleep 0.5
done
wait $TPID 2>/dev/null
{ echo "# watchdog: max polled RSS = $MAXRSS KB; wall = $(( $(date +%s) - START )) s; ${KILLED:+KILLED BY WATCHDOG: $KILLED}${KILLED:-completed}"; } >> "$LOG"
grep -E "RESULT|TOTAL|AUDIT|DISAGREE|Traceback|Error|maximum resident|# watchdog" "$LOG" | tr '\n' '|'; echo
