#!/bin/zsh
# downset_bip_predict_and_run.sh <tag> <script.py> <args...>
# 1) runs "<script.py> <args> --predict" (cheap, no linear algebra) and stores its output as the
#    prediction; 2) runs "<script.py> <args>" under /usr/bin/time -l via downset_bip_run.sh.
# Both commands are recorded in the log.  Logs go to ../logs/downset_bip_<tag>.log
TAG=$1; SCRIPT=$2; shift 2
PRED=$(mktemp)
{
  echo "prediction command: python3 $SCRIPT $* --predict"
  python3 "$SCRIPT" "$@" --predict
} > "$PRED" 2>&1
./downset_bip_run.sh "../logs/downset_bip_${TAG}.log" "$PRED" python3 "$SCRIPT" "$@"
rm -f "$PRED"
