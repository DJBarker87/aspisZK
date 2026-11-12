#!/bin/bash
# X2b: memory-stall watchdog for one Aeneas run of mine (read-only except for stopping that run). Stops the Aeneas
# process writing <log> when its RSS is above 6.1 GB and the log has not grown for four checks 30 s apart.
# Usage: fv_x2b_watch.sh <aeneas log path> <status file that ends the watch>
L=$1; ST=$2; last=-1; still=0
while [ ! -f $ST ]; do
  sleep 30
  pid=$(pgrep -f "aeneas -diagnose-translation.*$(dirname $(dirname $L))" | head -1)
  [ -z "$pid" ] && { still=0; continue; }
  rss=$(ps -o rss= -p $pid 2>/dev/null | tr -d ' '); sz=$(stat -c %s $L 2>/dev/null || echo 0)
  if [ "${rss:-0}" -gt 6100000 ] && [ "$sz" = "$last" ]; then still=$((still+1)); else still=0; fi
  last=$sz
  if [ $still -ge 4 ]; then echo "$(date -u +%FT%TZ) stopped aeneas pid $pid rss $rss log $sz" >> $(dirname $ST)/watchdog.log; kill $pid; still=0; fi
done
