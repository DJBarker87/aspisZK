#!/usr/bin/env bash
set -uo pipefail
BASE=/home/dombarker/project-offloads/aspis-r1-terminal-extraction-20261016
ATT="$BASE/attempt-a"
INPUT="$ATT/input"
OUT="$ATT/output/charon-a"
mkdir -p "$OUT" "$ATT/receipts/charon-a"
export PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin
export RUSTUP_TOOLCHAIN=nightly-2026-06-01
export CARGO_BUILD_JOBS=1
export CARGO_NET_OFFLINE=true
export CARGO_TARGET_DIR="$ATT/cargo-target"
CHARON=/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon
AENEAS=/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/bin/aeneas
O="$ATT/receipts/charon-a"
python3 - "$INPUT" "$O/source-preflight.json" <<'PY'
import hashlib,json,pathlib,sys
root=pathlib.Path(sys.argv[1]); m=json.loads((root/"source-pins.json").read_text()); bad=[]
for r in m["transitive_source_pins"]:
 p=root/r["copy_path"]
 if not p.is_file(): bad.append([r["copy_path"],"missing"]); continue
 h=hashlib.sha256(p.read_bytes()).hexdigest()
 if h!=r["copy_sha256"]: bad.append([r["copy_path"],h,r["copy_sha256"]])
w=m["wrapper"]; p=root/w["path"]
if hashlib.sha256(p.read_bytes()).hexdigest()!=w["sha256"]: bad.append([w["path"],"wrapper mismatch"])
json.dump({"rows":len(m["transitive_source_pins"]),"wrapper_sha256":w["sha256"],"bad":bad},open(sys.argv[2],"w"),indent=2)
if bad: sys.exit(1)
PY
if [ "$?" -ne 0 ]; then exit 90; fi
sha256sum "$CHARON" "$AENEAS" > "$O/tool-binaries.sha256"
sha256sum "$INPUT/Cargo.toml" "$INPUT/Cargo.lock" "$INPUT/crates/aspis-core/Cargo.toml" "$INPUT/crates/aspis-statement/Cargo.toml" > "$O/manifests.before.sha256"
start=$(date -u +%Y-%m-%dT%H:%M:%SZ); t0=$(date +%s%N)
CG=$(cut -d: -f3 /proc/self/cgroup); CGROOT=/sys/fs/cgroup$CG
printf 'start=%s\ncgroup=%s\ncommand=%s cargo --preset aeneas --mir built --sysroot default --start-from crate::extraction_probe::terminal_qm31_probe --dest-file %s/Terminal.llbc -- --manifest-path %s/Cargo.toml --package aspis-statement --features r0,pool-v1-kernel --no-default-features --release --lib --locked --offline\n' "$start" "$CGROOT" "$CHARON" "$OUT" "$INPUT" > "$O/metadata.txt"
/usr/bin/time -v timeout 300s "$CHARON" cargo --preset aeneas --mir built --sysroot default --start-from crate::extraction_probe::terminal_qm31_probe --dest-file "$OUT/Terminal.llbc" -- --manifest-path "$INPUT/Cargo.toml" --package aspis-statement --features r0,pool-v1-kernel --no-default-features --release --lib --locked --offline > "$O/command.log" 2>&1
rc=$?
t1=$(date +%s%N); end=$(date -u +%Y-%m-%dT%H:%M:%SZ)
python3 - "$t0" "$t1" "$O/metadata.txt" "$rc" "$end" <<'PY'
import sys
s,e,path,rc,end=sys.argv[1:]
with open(path,"a") as f:f.write(f"exit={rc}\nend={end}\nwall_seconds={(int(e)-int(s))/1e9:.3f}\n")
PY
sha256sum "$INPUT/Cargo.toml" "$INPUT/Cargo.lock" "$INPUT/crates/aspis-core/Cargo.toml" "$INPUT/crates/aspis-statement/Cargo.toml" > "$O/manifests.after.sha256"
[ -r "$CGROOT/memory.peak" ] && cat "$CGROOT/memory.peak" > "$O/memory.peak" || true
[ -r "$CGROOT/memory.swap.current" ] && cat "$CGROOT/memory.swap.current" > "$O/memory.swap.current" || true
[ -r "$CGROOT/memory.events" ] && cat "$CGROOT/memory.events" > "$O/memory.events" || true
[ -f "$OUT/Terminal.llbc" ] && sha256sum "$OUT/Terminal.llbc" > "$O/Terminal.llbc.sha256"
[ -f "$OUT/Terminal.llbc" ] && wc -c "$OUT/Terminal.llbc" > "$O/Terminal.llbc.bytes"
exit "$rc"
