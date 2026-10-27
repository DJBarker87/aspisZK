#!/bin/bash
# lead 2026-10-26: cross-stream quiet-window shim for `systemd-run` (installed as ~/.local/bin/systemd-run).
# While /home/dombarker/project-offloads/QUIET_WINDOW.json is in force ({"until": epoch} and now < until),
# wait OUTSIDE any scope (poll every 20 s, at most 35 minutes) before starting the requested scope, so the
# host is quiet for the timing gate. The window owner sets QUIET_WINDOW_OWNER=1 to bypass the wait.
# Otherwise this is a transparent exec of /usr/bin/systemd-run with the original arguments.
M=/home/dombarker/project-offloads/QUIET_WINDOW.json
if [ -z "$QUIET_WINDOW_OWNER" ] && [ -f "$M" ]; then
  waited=0
  while [ -f "$M" ] && [ $waited -lt 2100 ]; do
    until=$(python3 -c 'import json,sys
try: print(int(float(json.load(open(sys.argv[1])).get("until",0))))
except Exception: print(0)' "$M" 2>/dev/null)
    now=$(date +%s)
    [ -z "$until" ] && until=0
    [ "$now" -ge "$until" ] && break
    sleep 20; waited=$((waited+20))
  done
fi
exec /usr/bin/systemd-run "$@"
