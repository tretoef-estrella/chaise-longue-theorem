#!/bin/zsh
# _run.sh NAME 'command' — runs the command inside the watchdog from the mission folder, log in checks/NAME.log, and prints the tail.
cd /Users/rafa/Desktop/GREPY_IS_IN_THE_SKY
zsh material/vigia.sh checks/$1.log "cd checks && $2"
tail -${3:-40} checks/$1.log
