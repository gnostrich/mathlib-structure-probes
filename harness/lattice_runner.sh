#!/bin/bash
# Deterministic batch elaboration. DO NOT edit any file under RequestProject/Variants.
# Errors in the logs ARE the measurement data. Do not fix, prove, or repair anything.
set -u
mkdir -p logs/hb200k logs/hb50k
for f in RequestProject/Variants/*.lean; do
  b=$(basename "$f" .lean)
  lake env lean -DmaxHeartbeats=200000 "$f" > "logs/hb200k/$b.log" 2>&1
  echo "$b $?" >> logs/hb200k/exit.txt
  lake env lean -DmaxHeartbeats=50000  "$f" > "logs/hb50k/$b.log" 2>&1
  echo "$b $?" >> logs/hb50k/exit.txt
done
tar czf variant_logs.tar.gz logs
echo DONE: $(ls RequestProject/Variants/*.lean | wc -l) files, $(ls logs/hb200k/*.log | wc -l) + $(ls logs/hb50k/*.log | wc -l) logs
