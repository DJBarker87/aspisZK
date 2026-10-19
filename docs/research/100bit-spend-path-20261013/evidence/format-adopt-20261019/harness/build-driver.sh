#!/bin/sh
# usage: build-driver.sh <receipt-name> <note>
# Measurement driver: the Pool B1 measure driver (cu-bound2 host tree
# tools/r1-cost-probe-sweep, pool_gate.rs sha256 747cf4df...) patched by
# patch_driver_adopt.py, compiled against this branch's tree (release).
set -e
H=/home/dombarker/project-offloads/codex-r1-format-adopt-20261019
D=$H/src/tools/r1-cost-probe-adopt-driver
if [ ! -d $D ]; then
  cp -a /home/dombarker/project-offloads/codex-r1-cu-bound2-20261019/src/tools/r1-cost-probe-sweep $D
  python3 $H/harness/patch_driver_adopt.py $D
fi
export CARGO_TARGET_DIR=$H/driver-target
$H/harness/capped-run.sh $1 "$2" $D -- cargo build --release --offline --locked -j 4 --bin pool_gate --features private-leaf-salts
cp $H/driver-target/release/pool_gate $H/artifacts/pool_gate_adopt
sha256sum $D/src/bin/pool_gate.rs $H/artifacts/pool_gate_adopt; stat -c "%n %s" $H/artifacts/pool_gate_adopt
