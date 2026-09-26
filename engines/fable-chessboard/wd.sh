#!/bin/zsh
# usage: wd.sh script.m2 logfile   -- runs M2 with a 570 s watchdog, records RSS/time
script=$1; log=$2
/usr/bin/time -l /opt/homebrew/bin/M2 --script $script > $log 2> $log.time &
pid=$!
echo $pid > ${log%.log}.pid
for i in {1..570}; do
  sleep 1
  if ! kill -0 $pid 2>/dev/null; then wait $pid; echo "EXIT $? after ${i}s" >> $log; exit 0; fi
done
pkill -P $pid; kill -9 $pid 2>/dev/null; sleep 1
echo "WATCHDOG-KILLED at 570s" >> $log
pgrep -fl M2-binary >> $log || echo "pgrep: no M2 process remains" >> $log
