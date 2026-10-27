# Private Stage 3 copy: assigned range and task cap only; no shared launcher edited.
#!/bin/sh
# run-joint.sh <attempt> <Module> <env-id> [M-limit-MB] [MemoryMax G] [deps-fingerprint]
# run2-par.sh with the objects dir and LEAN_PATH taken from a named joint environment instead of
# objects2/environment-base.json.  Same reservation check, same slot locks (in-window: 22:30-14:00 London since 2026-10-19 (was 10:00), was 22:30-06:00) or global
# lock (outside), same systemd scope caps (MemoryHigh MX-2 G, MemoryMax MX G, MemorySwapMax 0,
# TasksMax 128), same timeout, same run2.py.  Evidence goes to $T/evidence/{sha,out,time}-<A>.
# Environments (H/env/<id>.json, H/objects-<id>):
#   A  privacy base: H/objects-A : objects2 : environment-base LEAN_PATH
#   C  spend sampler overlay: H/objects-C : correct-c import-overlay : correct-c search path
#   J  unified base (LOG D63): J/objects : AspisFormal consolidation packages : Aeneas 4.32 port
#      backend : Lean core, sources J/sources (J = aspis-joint-20261019); attempts 5000-5799 (extended by the lead)
# Refuses a (source sha, env-id, deps-fingerprint) triple that was already sent; the fingerprint
# (from joint-drive.py: sha256 over the module's imports and their object sha256s) makes a
# dependent rebuild after a dependency changed a new input, never an unchanged rerun.
set -u
T=/home/dombarker/project-offloads/aspis-fs-generic-20261006
H=/home/dombarker/project-offloads/r1-privacy-build-integration-20261019
A=$1; M=$2; E=$3; ML=${4:-7000}; MX=${5:-7}; FP=${6:-none}; NSLOTS=4
if [ "$E" = J ]; then
  case "$A" in 1156[3-9]|115[7-9][0-9]|11[6-9][0-9][0-9]|12[0-3][0-9][0-9]|14[4-7][0-9][0-9]) ;; *) echo "attempt $A outside assigned 11563-11599"; exit 64;; esac
  J=/home/dombarker/project-offloads/aspis-joint-20261019; SRCROOT="$J/sources"; OBJ="$J/objects"
else
  case "$A" in 45[2-9][0-9]) ;; *) echo "attempt $A outside 4520-4599"; exit 64;; esac
  SRCROOT="$H/sources"; OBJ="$H/objects-$E"
fi
[ -e "$T/evidence/out-$A.log" ] && { echo "attempt $A already used"; exit 65; }
SRC="$SRCROOT/$M.lean"; ENVJ="$H/env/$E.json"
[ -f "$SRC" ] && [ -f "$ENVJ" ] && [ -d "$OBJ" ] || { echo "missing source/env/objects"; exit 66; }
S=$(sha256sum "$SRC" | cut -d' ' -f1)
if grep -q "^$S $E [0-9]* [^ ]* $FP\$" "$H/evidence/sent.txt" 2>/dev/null || { [ "$FP" = none ] && grep -q "^$S $E " "$H/evidence/sent.txt" 2>/dev/null; }; then echo "REFUSED: $M sha $S already sent in env $E with deps $FP"; exit 67; fi
hm=$(TZ=Europe/London date +%H%M)
inwin=0; if [ "$hm" -ge 2230 ] || [ "$hm" -lt 1400 ]; then inwin=1; fi
N=/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy
RE=/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/native-drop/lean
mkdir -p "$RE"
mkdir -p "$OBJ/$(dirname $M)"
sha256sum "$SRC" > "$T/evidence/sha-$A.txt"
echo "$S $E $A $M $FP" >> "$H/evidence/sent.txt"
run() {
  python3 "$N/reservation.py" "$RE/$A-admission-before.json" --requested-bytes 7516192768 || return $?
  systemd-run --user --scope --quiet -p MemoryHigh=$((MX-2))G -p MemoryMax=${MX}G -p MemorySwapMax=0 -p TasksMax=64 \
    python3 "$N/barrier.py" "$RE/$A-admission-barrier.json" /usr/bin/time -v -o "$T/evidence/time-$A.log" timeout 900 python3 "$T/evidence/run2.py" "$ENVJ" "$OBJ" "$SRCROOT" "$OBJ/$M.olean" "$SRC" "$ML" > "$T/evidence/out-$A.log" 2>&1
  echo "exit=$?" >> "$T/evidence/out-$A.log"
}
if [ $inwin = 1 ]; then
  LOCK=""; while [ -z "$LOCK" ]; do
    for s in $(seq 1 $NSLOTS); do f=/tmp/aspis-r0-lean-slot-$s.lock
      exec 9>"$f"; if flock -n 9; then LOCK=$f; break; fi; done
    [ -z "$LOCK" ] && sleep 20
  done
  echo "slot: $LOCK"; run
else
  exec 9>/tmp/aspis-r0-lean.lock; flock 9; LOCK=global; run
fi
echo "window=$inwin slot=$LOCK env=$E launcher=run-joint.sh" >> "$T/evidence/out-$A.log"
tail -n 60 "$T/evidence/out-$A.log"
grep -E "Elapsed|Maximum resident|Swaps|Exit status" "$T/evidence/time-$A.log"
