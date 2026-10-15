#!/usr/bin/env bash
set -euo pipefail
ulimit -c 0
w=/home/dombarker/project-offloads/aspis-r1-route-guard-3c79ec30f-20261015
src="$w/source"
evidence="$w/results/route-guard-unit"
target=/home/dombarker/project-offloads/aspis-100bit-field-parser-candidate-20261014/cargo-target-v152
cargo=/home/dombarker/.cargo/bin/cargo
export PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin
mkdir -p "$evidence"
test "$(sha256sum "$src/programs/r1-cost-probe/src/lib.rs" | cut -d' ' -f1)" = 36d36ee707f565df675db2ef7b2d27467f8b79bb99142c4b21d6fb7cc81910c9
printf 'head=%s\n' 3c79ec30fa44f408c716bb345050c137e907fa67 > "$evidence/source-info.txt"
printf 'lib.rs=%s\n' "$(sha256sum "$src/programs/r1-cost-probe/src/lib.rs" | cut -d' ' -f1)" >> "$evidence/source-info.txt"
printf 'Cargo.lock=%s\n' "$(sha256sum "$src/Cargo.lock" | cut -d' ' -f1)" >> "$evidence/source-info.txt"
printf 'start_utc=%s\n' "$(date -u +%FT%TZ)" >> "$evidence/source-info.txt"
printf 'memory_before:\n' >> "$evidence/source-info.txt"
free -b >> "$evidence/source-info.txt"
printf 'cargo_version=' >> "$evidence/source-info.txt"
"$cargo" --version >> "$evidence/source-info.txt"
printf 'rustc_version=' >> "$evidence/source-info.txt"
rustc --version >> "$evidence/source-info.txt"
cd "$src"
set +e
systemd-run --user --scope --quiet -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=128 \
  /usr/bin/time -v -o "$evidence/test.time.log" /usr/bin/env CARGO_TARGET_DIR="$target" CARGO_BUILD_JOBS=2 \
  "$cargo" test --release --locked --offline --manifest-path "$src/programs/r1-cost-probe/Cargo.toml" \
  -p aspis-r1-cost-probe-program --features pool-adapter,private-leaf-salts --jobs 2 --lib \
  pool_adapter_rejects_legacy_tags_before_borrowing_accounts \
  > "$evidence/test.out.log" 2>&1
test_status=$?
systemd-run --user --scope --quiet -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=128 \
  /usr/bin/time -v -o "$evidence/nonpool-check.time.log" /usr/bin/env CARGO_TARGET_DIR="$target" CARGO_BUILD_JOBS=2 \
  "$cargo" check --release --locked --offline --manifest-path "$src/programs/r1-cost-probe/Cargo.toml" \
  -p aspis-r1-cost-probe-program --jobs 2 \
  > "$evidence/nonpool-check.out.log" 2>&1
check_status=$?
set -e
printf 'test_exit=%s\nnonpool_check_exit=%s\nend_utc=%s\n' "$test_status" "$check_status" "$(date -u +%FT%TZ)" >> "$evidence/source-info.txt"
if [ "$test_status" -ne 0 ] || [ "$check_status" -ne 0 ]; then exit 1; fi
