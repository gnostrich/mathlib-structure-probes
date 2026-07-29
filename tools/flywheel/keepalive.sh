#!/bin/sh
# Keeps the session environment warm and records Flywheel graph liveness.
# One verify call every 15 minutes for 24 hours. Read-only against the API.
SP="/tmp/claude-0/-home-user-Structure-Backprop/a747742e-9a2f-5c79-9f64-ed3bc601f93e/scratchpad"
i=0
while [ "$i" -lt 96 ]; do
  date -u +"%Y-%m-%dT%H:%M:%SZ tick $i" >> "$SP/fw_keepalive.log"
  python3 "$SP/fw_sync.py" --verify >> "$SP/fw_keepalive.log" 2>&1
  i=$((i + 1))
  sleep 900
done
echo "keepalive finished after 24h"
