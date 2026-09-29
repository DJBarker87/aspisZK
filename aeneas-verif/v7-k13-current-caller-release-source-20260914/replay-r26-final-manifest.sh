#!/usr/bin/env sh
set -eu

bundle=${1:?usage: replay-r26-final-manifest.sh BUNDLE_DIR OUTPUT_DIR}
output=${2:?usage: replay-r26-final-manifest.sh BUNDLE_DIR OUTPUT_DIR}

proof="$bundle/proof-r26"
generated="$bundle/generated/V7CallerCurrentReleaseR26"
arith=/home/dombarker/project-offloads/v7-gate-closure-prechallenge-return-r22/arithmetic-lean432-cache-current
backend=/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/aeneas-full/backends/lean
aspis=/home/dombarker/project-offloads/aspis-v7-root-sweep-20260909/AspisFormal
lean=/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean

if [ -e "$output" ]; then
  echo "refusing to reuse final replay output: $output" >&2
  exit 2
fi
mkdir -p "$output/V7CallerCurrentReleaseR26"

cd "$bundle"
sha256sum -c FINAL-MANIFEST.sha256

if grep -En '\b(sorry|admit|native_decide)\b|^[[:space:]]*axiom[[:space:]]' \
    $(awk '{print $2}' FINAL-MANIFEST.sha256 | grep '/.*\.lean$'); then
  echo "forbidden proof shortcut found in frozen manifest" >&2
  exit 3
fi

packages=""
for directory in "$aspis"/.lake/packages/*/.lake/build/lib/lean \
    "$backend"/.lake/packages/*/.lake/build/lib/lean; do
  packages="${packages:+$packages:}$directory"
done
export LEAN_PATH="$output:$arith:$aspis/.lake-root-sweep/lib/lean:$backend/.lake/build/lib/lean:$packages"

compile_generated() {
  module=$1
  echo "START generated/$module"
  /usr/bin/time -f "RESULT target=generated/$module exit=%x wall_s=%e peak_kib=%M swaps=%W" \
    "$lean" -o "$output/V7CallerCurrentReleaseR26/$module.olean" \
      "$generated/$module.lean"
}

compile_generated TypesExternal
compile_generated Types
compile_generated FunsExternal
compile_generated MutableIteratorCompat
compile_generated Funs

order="$output/proof-order.txt"
python3 - "$proof" > "$order" <<'PY'
from pathlib import Path
import sys

proof = Path(sys.argv[1])
modules = {path.stem: path for path in proof.glob("*.lean")}
dependencies = {module: [] for module in modules}
for module, path in modules.items():
    for line in path.read_text().splitlines():
        if line.startswith("import "):
            dependency = line.split()[1]
            if dependency in modules:
                dependencies[module].append(dependency)

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

visit("V7CallerCurrentReleaseR26AcceptedTerminalEndToEnd")
for module in order:
    print(module)
PY

target_count=$(wc -l < "$order" | tr -d ' ')
if [ "$target_count" != 117 ]; then
  echo "unexpected proof closure size: $target_count" >&2
  exit 4
fi

while IFS= read -r module; do
  echo "START proof/$module"
  /usr/bin/time -f "RESULT target=proof/$module exit=%x wall_s=%e peak_kib=%M swaps=%W" \
    "$lean" -o "$output/$module.olean" "$proof/$module.lean"
done < "$order"

echo "FINAL target=V7CallerCurrentReleaseR26AcceptedTerminalEndToEnd modules=$target_count status=passed"
