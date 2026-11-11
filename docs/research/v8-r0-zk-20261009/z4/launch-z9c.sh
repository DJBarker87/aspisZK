#!/bin/bash
# Z9c launcher (D38.5), copied from launch-r1p.sh.
# run beside this capped probe; any other non-Lean probe (cargo/rustc/release binary/z10)
# blocks the launch; the sum of MemoryMax reservations incl. ours must stay <= 48 GiB.
set -u
S=/home/dombarker/project-offloads/aspis-cert-20261019
MODE=$1; REV=$2
cd $S/repo-$REV
echo "GATE_CHECK $(date -Is)"
total=4294967296; block=""
for sc in $(systemctl --user list-units --type=scope --state=active --no-legend --plain | awk '{print $1}' | grep -v '^init.scope$'); do
  mm=$(systemctl --user show -p MemoryMax --value $sc); cgp=$(systemctl --user show -p ControlGroup --value $sc)
  cmds=$(for p in $(cat /sys/fs/cgroup$cgp/cgroup.procs 2>/dev/null); do tr '\0' ' ' < /proc/$p/cmdline 2>/dev/null; echo; done)
  echo "scope $sc MemoryMax=$mm"; echo "$cmds" | cut -c1-160 | sed 's/^/   /'
  [ "$mm" = infinity ] && block="$block $sc(uncapped)"
  [ "$mm" != infinity ] && total=$((total+mm))
  if echo "$cmds" | grep -qE 'cargo|rustc|target/release/|/z10|run-z[0-9]'; then block="$block $sc(non-lean-probe)"; fi
done
echo "reservation_sum_bytes=$total limit=51539607552"
[ $total -gt 51539607552 ] && block="$block reservation"
if [ -n "$block" ]; then echo "GATE_FAIL$block"; exit 3; fi
echo GATE_OK; free -g | head -2

/usr/bin/time -v -o $S/z9c-$MODE-$REV-time.txt systemd-run --user --scope --unit=aspis-z9c-$MODE-$REV \
  -p MemoryHigh=3G -p MemoryMax=4G -p MemorySwapMax=0 -p TasksMax=64 \
  python3 docs/research/v8-r0-zk-20261009/z4/run-z9c.py --out $S/z9c-$MODE-$REV --revision $REV $([ "$MODE" = preflight ] && echo --preflight)
echo "EXIT $? $(date -Is)"
