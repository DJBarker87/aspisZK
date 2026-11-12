#!/bin/bash
# Gate C launcher: waits until the host's 1-minute and 5-minute load averages are both under 2, for at
# most 90 minutes after the end of the other gates (mtime of the later CHAIN_*.DONE); then runs five
# interleaved rounds (before, after) in one capped scope. If the host does not become quiet in time,
# writes TIMING_NOT_RUN and starts nothing.
W=/home/dombarker/project-offloads/codex-pv-aspis-rewrite2-20261112; cd $W
end=$(stat -c %Y CHAIN_before.DONE CHAIN_after.DONE | sort -n | tail -1); deadline=$((end+5400))
while true; do
  read l1 l5 rest < /proc/loadavg
  echo "$(date -u +%FT%TZ) load $l1 $l5" >> timing_wait.log
  if awk -v a=$l1 -v b=$l5 'BEGIN{exit !(a<2 && b<2)}'; then break; fi
  if [ $(date +%s) -ge $deadline ]; then echo "not quiet by $(date -u +%FT%TZ); last load $l1 $l5" > TIMING_NOT_RUN; exit 3; fi
  sleep 30
done
PV_SRC_REV="before and after binaries" bash $W/tools/job.sh G-timing 7200 "gate C: fixture prover wall time, before and after binaries interleaved, 5 rounds, seed 3; time expected in proof generation (release binaries)" bash $W/tools/timing.sh rebase 5 3 before after
echo "timing exit $?" > TIMING_DONE
