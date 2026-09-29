#!/usr/bin/env sh
set -eu

bundle=${1:?usage: replay-r28-r29-bridge.sh BUNDLE_DIR REPO_ROOT R26_OLEAN_DIR OUTPUT_DIR}
repo=${2:?usage: replay-r28-r29-bridge.sh BUNDLE_DIR REPO_ROOT R26_OLEAN_DIR OUTPUT_DIR}
r26_olean=${3:?usage: replay-r28-r29-bridge.sh BUNDLE_DIR REPO_ROOT R26_OLEAN_DIR OUTPUT_DIR}
output=${4:?usage: replay-r28-r29-bridge.sh BUNDLE_DIR REPO_ROOT R26_OLEAN_DIR OUTPUT_DIR}

generated="$bundle/generated/V7ProductionSnapshotObserverR28"
proof="$bundle/proof-r28"
proof_r26="$bundle/proof-r26"
proof_r30="$bundle/proof-r30"
old_callbacks="$repo/aeneas-verif/v7-tag73-current-caller-source-20260830/proof"
stage="$output/staged-r29"
arith=/home/dombarker/project-offloads/v7-gate-closure-prechallenge-return-r22/arithmetic-lean432-cache-current
backend=/home/dombarker/project-offloads/v7-gate-closure-prechallenge-return-r22/aeneas-lean-formatter-unit-r26
aspis=/home/dombarker/project-offloads/aspis-v7-root-sweep-20260909/AspisFormal
lean=/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean

if [ -e "$output" ]; then
  echo "refusing to reuse replay output: $output" >&2
  exit 2
fi
mkdir -p "$output/V7ProductionSnapshotObserverR28"

python3 "$bundle/toolchain/stage-r29-production-callbacks.py" \
  "$old_callbacks" "$stage"

packages=""
for directory in "$aspis"/.lake/packages/*/.lake/build/lib/lean \
    "$backend"/.lake/packages/*/.lake/build/lib/lean; do
  packages="${packages:+$packages:}$directory"
done
export LEAN_PATH="$output:$r26_olean:$arith:$aspis/.lake-root-sweep/lib/lean:$backend/.lake/build/lib/lean:$packages"

compile_to() {
  source=$1
  target=$2
  mkdir -p "$(dirname "$target")"
  echo "START $source"
  /usr/bin/time -f "RESULT target=$source exit=%x wall_s=%e peak_kib=%M swaps=%W" \
    "$lean" -o "$target" "$source"
}

compile_to "$generated/TypesExternal.lean" \
  "$output/V7ProductionSnapshotObserverR28/TypesExternal.olean"
compile_to "$generated/Types.lean" \
  "$output/V7ProductionSnapshotObserverR28/Types.olean"

order="$output/r29-proof-order.txt"
python3 - "$stage" > "$order" <<'PY'
from pathlib import Path
import re
import sys

root = Path(sys.argv[1])
modules = {}
for path in root.rglob("*.lean"):
    if path.name.endswith("_Template.lean"):
        continue
    module = path.relative_to(root).with_suffix("").as_posix().replace("/", ".")
    modules[module] = path

dependencies = {module: [] for module in modules}
for module, path in modules.items():
    for line in path.read_text().splitlines():
        match = re.fullmatch(r"import ([A-Za-z0-9_'.]+)", line.strip())
        if match and match.group(1) in modules:
            dependencies[module].append(match.group(1))

seen = set()
active = set()
order = []

def visit(module):
    if module in seen:
        return
    if module in active:
        raise RuntimeError(f"import cycle at {module}")
    active.add(module)
    for dependency in dependencies[module]:
        visit(dependency)
    active.remove(module)
    seen.add(module)
    order.append(module)

visit("V7ProductionCallbacksR29.FunsChunk44")
for module in order:
    print(module)
PY

while IFS= read -r module; do
  relative=$(printf '%s' "$module" | tr . /)
  compile_to "$stage/$relative.lean" "$output/$relative.olean"
done < "$order"

compile_to "$generated/FunsExternal.lean" \
  "$output/V7ProductionSnapshotObserverR28/FunsExternal.olean"
compile_to "$generated/Funs.lean" \
  "$output/V7ProductionSnapshotObserverR28/Funs.olean"
compile_to "$proof_r26/V7CallerCurrentReleaseR26AcceptedPrechallengeDispatch.lean" \
  "$output/V7CallerCurrentReleaseR26AcceptedPrechallengeDispatch.olean"
compile_to "$proof_r26/V7CallerCurrentReleaseR26AcceptedInnerToPrechallenge.lean" \
  "$output/V7CallerCurrentReleaseR26AcceptedInnerToPrechallenge.olean"
compile_to "$proof/V7ProductionSnapshotObserverR28SourceBridge.lean" \
  "$output/V7ProductionSnapshotObserverR28SourceBridge.olean"
compile_to "$proof/V7ProductionSnapshotObserverR28ToR26Prechallenge.lean" \
  "$output/V7ProductionSnapshotObserverR28ToR26Prechallenge.olean"
compile_to "$proof/V7ProductionSnapshotObserverR28AcceptedTail.lean" \
  "$output/V7ProductionSnapshotObserverR28AcceptedTail.olean"
compile_to "$proof_r30/V7CallerCurrentReleaseR30FixedFieldCanonical.lean" \
  "$output/V7CallerCurrentReleaseR30FixedFieldCanonical.olean"
compile_to "$proof_r30/V7CallerCurrentReleaseR30RelationFieldInnerCanonical.lean" \
  "$output/V7CallerCurrentReleaseR30RelationFieldInnerCanonical.olean"
compile_to "$proof_r30/V7CallerCurrentReleaseR30RelationFieldsCanonical.lean" \
  "$output/V7CallerCurrentReleaseR30RelationFieldsCanonical.olean"
compile_to "$proof_r30/V7ProductionSnapshotObserverR30RelationRowsCanonical.lean" \
  "$output/V7ProductionSnapshotObserverR30RelationRowsCanonical.olean"

echo "FINAL target=V7ProductionSnapshotObserverR30RelationRowsCanonical status=passed"
