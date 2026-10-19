#!/usr/bin/env bash
set -euo pipefail
ROOT=/home/dombarker/project-offloads/aspis-r1-terminal-copy-indexed-20261016
BASE=/home/dombarker/project-offloads/aspis-r1-j1a-terminal-regression-20261016/after-sbf-fresh-artifacts/aspis_r1_cost_probe_program.so
BASE_RECEIPT=/home/dombarker/project-offloads/aspis-r1-j1a-terminal-regression-20261016/runs/after-sbf-fresh/receipt.json
CAND="$ROOT/runs/candidate-sbf/artifacts/aspis_r1_cost_probe_program.so"
CAND_RECEIPT="$ROOT/runs/candidate-sbf/receipt.json"
BIN="$ROOT/cargo-target/release/r18_case_replay"
P3="$ROOT/p3-case-fixtures"
OUT="$ROOT/runs/p3-paired-verifier-b"
REV=a8930e677bc745854b9f693b5628c8a8bd2ac848
sha() { sha256sum "$1" | awk '{print $1}'; }
test "$(sha "$BASE")" = 2c031d0040a3bf739b58591b2a20dc68f04722550fd49b79d4fd7eb8e5dfee9f
test "$(sha "$CAND")" = d346de4aa5a122f7ad0d2dde819ec416d2e479065490e5a84f970c534ea4220d
test "$(sha "$BIN")" = 8068af36cb9b0e38456457db7004c94f3d2a0ea1212b0c97746f790a26f60615
test "$(jq -r '.artifacts["after-sbf-fresh-artifacts/aspis_r1_cost_probe_program.so"]' "$BASE_RECEIPT")" = "$(sha "$BASE")"
test "$(jq -r .artifact_sha256 "$CAND_RECEIPT")" = "$(sha "$CAND")"
test ! -e "$OUT"
mkdir -p "$OUT"
cat > "$OUT/cases.tsv" <<'CASES'
transfer-13-os-task	f04b11c9e5b725749ed8810c529cdeb25aab2161bca4dc3378647fc089b53ed3	f6bcd49446f1077d2c5ed4be940e91f0be444efc5ae83024ec0700b8c205c331	13	transfer
transfer-255-os-task	3d68309b72bf61f0cd36e02b49b4c7d3f8377df81dd7c9b24a25e44ba722908e	e201be4a028d74258c5344e7395bfabf7568af4ee7df0ec0c7b695f02fbacb15	255	transfer
withdrawal-255-os-task	dd83a7260a3a619cbe712ec591574ac625c0a38980c4c81ff6d3b26f8e13b853	7c2c27e135fa537776fad1457047f6c86ec351d64a8f0c6053674d2c2631200a	255	withdrawal
withdrawal-1023-os-task	7bab9c8b102e6527118c589c984ef2b575bb046f18eaab4dc9c2926ec27d36f2	456bcde525f9e6947d9fc326daf3c3e01c8871cc4bf3d9fae6ab816980cb8f48	1023	withdrawal
CASES
cat > "$OUT/command.txt" <<EOF
ROOT=$ROOT
BASE=$BASE
BASE_RECEIPT=$BASE_RECEIPT
CAND=$CAND
CAND_RECEIPT=$CAND_RECEIPT
HARNESS=$BIN
source_revision=$REV
scope: MemoryHigh=8G MemoryMax=10G MemorySwapMax=0 TasksMax=128; four paired verifier-only cases, no proof generation, no settlement
EOF
free -b > "$OUT/host-memory-before.txt"
ps -eo pid,rss,comm,args --sort=-rss | head -30 > "$OUT/processes-before.txt"
cat /proc/meminfo | head -12 > "$OUT/meminfo-before.txt"
CGREL=$(awk -F: '$1=="0" {print $3}' /proc/self/cgroup)
CG=/sys/fs/cgroup$CGREL
printf 'cgroup=%s\n' "$CGREL" > "$OUT/scope-preflight.txt"
printf 'memory.high=%s\nmemory.max=%s\nmemory.swap.max=%s\npids.max=%s\nmemory.current=%s\n' "$(cat "$CG/memory.high")" "$(cat "$CG/memory.max")" "$(cat "$CG/memory.swap.max")" "$(cat "$CG/pids.max")" "$(cat "$CG/memory.current")" >> "$OUT/scope-preflight.txt"
test "$(cat "$CG/memory.high")" = 8589934592
test "$(cat "$CG/memory.max")" = 10737418240
test "$(cat "$CG/memory.swap.max")" = 0
test "$(cat "$CG/pids.max")" = 128
printf 'case\tproof_sha\tpublic_sha\tindex\tvariant\texit\n' > "$OUT/results.tsv"
while IFS=$'\t' read -r case proofsha publicsha index variant; do
  d="$OUT/$case"; mkdir -p "$d"
  proof="$P3/$case/proof.bin"; public="$P3/$case/public.bin"
  test "$(sha "$proof")" = "$proofsha"
  test "$(sha "$public")" = "$publicsha"
  printf '%s\t%s\t%s\t%s\t%s\n' "$case" "$proofsha" "$publicsha" "$index" "$variant" > "$d/input-pins.tsv"
  cat > "$d/command.txt" <<EOCMD
/usr/bin/time -v -o $d/time.log env ASPIS_SOURCE_REVISION=$REV ASPIS_R18_BEFORE_REVISION=42e5ca2011c39ee9770afc798282ff861b092428 ASPIS_R18_AFTER_REVISION=$REV ASPIS_R18_BEFORE_BUILD_RECEIPT=$BASE_RECEIPT ASPIS_R18_AFTER_BUILD_RECEIPT=$CAND_RECEIPT $BIN $BASE $CAND $proof $public $proofsha $publicsha $index $variant $d/r18-output
EOCMD
  set +e
  /usr/bin/time -v -o "$d/time.log" env ASPIS_SOURCE_REVISION="$REV" ASPIS_R18_BEFORE_REVISION=42e5ca2011c39ee9770afc798282ff861b092428 ASPIS_R18_AFTER_REVISION="$REV" ASPIS_R18_BEFORE_BUILD_RECEIPT="$BASE_RECEIPT" ASPIS_R18_AFTER_BUILD_RECEIPT="$CAND_RECEIPT" "$BIN" "$BASE" "$CAND" "$proof" "$public" "$proofsha" "$publicsha" "$index" "$variant" "$d/r18-output" > "$d/run.log" 2>&1
  ex=$?
  set -e
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$case" "$proofsha" "$publicsha" "$index" "$variant" "$ex" >> "$OUT/results.tsv"
  test "$ex" = 0
  test -s "$d/r18-output/comparison.json"
done < "$OUT/cases.tsv"
printf 'memory.peak=%s\nswap.current=%s\nmemory.events:\n%s\n' "$(cat "$CG/memory.peak")" "$(cat "$CG/memory.swap.current")" "$(cat "$CG/memory.events")" > "$OUT/scope-result.txt"
