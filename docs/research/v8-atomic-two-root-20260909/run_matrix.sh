#!/usr/bin/env bash
set -euo pipefail
ex="$(cd "$(dirname "$0")" && pwd)";rt="$(cd "$ex/../../.." && pwd)"
[[ "$rt" == /home/dombarker/project-offloads/aspis-v8-atomic-two-root-20260909 && ! -e "$rt/.git" ]] || exit 2
[[ $# == 1 && ! -e "$1" ]] || exit 2
out="$1";mkdir "$out"
driver="$rt/docs/research/v8-no-work-100-20260907/experiments/performance-svm/target/release/aspis-v7-pair-forest-combined-rejection"
cd "$rt"
python3 "$ex/artifact_guard.py" check
python3 - "$ex" <<'PY'
import hashlib,json,pathlib,sys
ex=pathlib.Path(sys.argv[1]);root=ex.parents[2]
x=json.loads((ex/'evidence/artifact-provenance.json').read_text())
for name,a in x['artifacts'].items():
 assert hashlib.sha256((root/'artifacts'/name).read_bytes()).hexdigest()==a['sha256'],name
print('Immutable retained artifacts match pinned evidence')
PY
for count in 13 255;do for seed in 1 2 3;do
 case "$count-$seed" in 13-1) b=13;;13-2) b=0;;13-3) b=255;;255-1) b=13;;255-2) b=1023;;255-3) b=4095;;esac
 name="transfer-$count-$seed"
 systemd-run --user --scope --unit="aspis-atomic-$name-$(date +%s)-$$" -p MemoryHigh=3G -p MemoryMax=4G -p MemorySwapMax=0 /usr/bin/time -v \
  env NO_DNA=1 ASPIS_COMPLETE_TX_LIMIT=1200000 ASPIS_ATOMIC_EXPERIMENT="$ex" ASPIS_ATOMIC_DEEP=1 ASPIS_ATOMIC_B_COUNT="$b" \
  "$driver" artifacts/pool.so artifacts/verifier.so artifacts/registry.so artifacts/double.so "$out/$name.json" "fixtures/$name.bin" success 1400000 asq8 "$count" transfer >"$out/$name.log" 2>&1
done;done
for seed in 1 2 3;do
 name="ordinary-13-$seed"
 systemd-run --user --scope --unit="aspis-atomic-$name-$(date +%s)-$$" -p MemoryHigh=3G -p MemoryMax=4G -p MemorySwapMax=0 /usr/bin/time -v \
  env NO_DNA=1 ASPIS_COMPLETE_TX_LIMIT=1200000 ASPIS_ATOMIC_EXPERIMENT="$ex" ASPIS_ATOMIC_DEEP=0 ASPIS_ATOMIC_B_COUNT=13 \
  "$driver" artifacts/pool.so artifacts/verifier.so artifacts/registry.so artifacts/double.so "$out/$name.json" "proving/proofs/proof-$seed.bin" success 1400000 asq8 13 transfer >"$out/$name.log" 2>&1
done
sha256sum "$driver" "$rt/artifacts/inbox/aspis_v8_atomic_inbox.so" "$ex/driver.rs" "$ex/inbox/lib.rs" >"$out/artifact-hashes.txt"
