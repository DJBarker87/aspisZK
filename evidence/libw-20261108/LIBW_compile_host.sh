#!/usr/bin/env bash
# Host compile recipe for LIBW_WeakPerEnv.lean (single file, focused job).
# Reuses the LIBB_L344 environment (LIBB_GATE_IMPORT, which imports LIBB_V2Star)
# verbatim from evidence/libb-20261111/LIBB_L344.json, with one new output dir
# prepended to LEAN_PATH. No dependency is rebuilt.
# Run on the build host from a checkout of branch codex/cx-libw-20261108 with
# evidence/libb-20261111 and evidence/libw-20261108 present.
set -euo pipefail
REPO=${REPO:?set REPO to the checkout root on the host}
OFF=/home/dombarker/project-offloads/codex-cx-libw-20261108
LIBB=/home/dombarker/project-offloads/codex-cx-libb-20261111
mkdir -p "$OFF/LIBW_generated" "$OFF/LIBW_objects" "$OFF/LIBW_tmp"
cp "$REPO/evidence/libw-20261108/LIBW_WeakPerEnv.lean" "$OFF/LIBW_generated/"
test -f "$LIBB/LIBB_objects/LIBB_V2Star.olean"
LP=$(python3 -I -c 'import json,sys;print(json.load(open(sys.argv[1]))["env"]["LEAN_PATH"])' \
  "$REPO/evidence/libb-20261111/LIBB_L344.json")
TC=/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0
cd "$OFF"
git -C "$REPO" rev-parse HEAD > LIBW_L001.rev
systemd-run --user --scope --quiet -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 \
  /usr/bin/env -i LEAN_SYSROOT="$TC" PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin \
  TMPDIR="$OFF/LIBW_tmp" LEAN_PATH="$OFF/LIBW_objects:$LP" \
  /usr/bin/time -v -o LIBW_L001.time \
  "$TC/bin/lake" env lean -j1 -M7000 -DElab.async=false -R LIBW_generated \
  -o LIBW_objects/LIBW_WeakPerEnv.olean LIBW_generated/LIBW_WeakPerEnv.lean \
  > LIBW_L001.stdout 2>&1 && rc=0 || rc=$?
echo "exit=$rc" > LIBW_L001.exit
cat LIBW_L001.exit; grep -E 'Elapsed|Maximum resident' LIBW_L001.time
# Accept only: exit=0, no error, 19 axiom lines, each within {propext, Classical.choice, Quot.sound}.
python3 -I - LIBW_L001.stdout <<'PY'
import re,sys
t=open(sys.argv[1]).read()
ok={"propext","Classical.choice","Quot.sound"}
lines=[l for l in t.splitlines() if "depends on axioms" in l or "does not depend on any axioms" in l]
bad=[l for l in lines if "depends on axioms" in l and not set(x.strip() for x in re.search(r"\[(.*)\]",l).group(1).split(","))<=ok]
err="error" in t
print("axiom_lines",len(lines),"bad",bad,"error",err)
sys.exit(0 if len(lines)==19 and not bad and not err else 1)
PY
