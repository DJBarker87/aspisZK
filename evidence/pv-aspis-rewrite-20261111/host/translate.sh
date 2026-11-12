#!/bin/bash
# Gate D for one root set. usage: translate.sh TAG [--opaque ITEM]...
#   roots/TAG.txt -> Charon (own scope) -> llbc/TAG.llbc -> tool k2 (own scope) -> emit/TAG/generated
# Charon 0.1.223 (hash asserted in charon_rw.py), toolchain nightly-2026-06-01, client configuration, checks off.
# Translator: aeneas-combined-k2, sha256 7271db7e... (asserted here), command line of the earlier emissions.
W=/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111
K2=/home/dombarker/project-offloads/codex-pv-combined-20261111/toolsrc/bin/aeneas-combined-k2
tag=$1; shift
cd $W; mkdir -p llbc tgt emit
[ "$(sha256sum < $K2 | cut -d' ' -f1)" = 7271db7e48ec710d56e857f862de42c301cee3f3b7fd17e943918de102fb3741 ] || { echo K2-HASH-MISMATCH; exit 3; }
export PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin RUSTUP_TOOLCHAIN=nightly-2026-06-01 CARGO_NET_OFFLINE=true
export PV_ROOTS_FILE=$W/roots/$tag.txt PV_SRC_REV=$(cat $W/SOURCE_REVISION)
# One cargo target directory per root set: with a shared one cargo finds every unit fresh and never calls the driver.
python3 $W/tools/run_job.py C-$tag "Charon on the rewritten source, client configuration (checks OFF), start roots = roots/$tag.txt; time expected in cargo compilation then the charon-driver pass" 2400 $W/${PV_SRC_DIR:-src} -- python3 $W/tools/charon_rw.py $W/${PV_SRC_DIR:-src} $W/llbc/$tag.llbc $W/tgt/$tag "$@" > $W/runs/C-$tag.driver.log 2>&1
ce=$(python3 -c "import json;print(json.load(open('runs/C-$tag/receipt.json'))['exit'])")
echo "charon exit $ce" > runs/$tag.STATUS
if [ "$ce" = 0 ] && [ -s llbc/$tag.llbc ]; then
  mkdir -p emit/$tag; ln -s $W/llbc/$tag.llbc emit/$tag/ProverPin2.llbc
  python3 $W/tools/run_job.py A-$tag "tool k2 (7271db7e) on llbc/$tag.llbc, no -abort-on-error; time expected in symbolic execution and Lean emission" 900 $W/emit/$tag -- $K2 -sequential -no-progress-bar -backend lean -namespace ProverPin2 -dest generated -split-files ProverPin2.llbc > $W/runs/A-$tag.driver.log 2>&1
  echo "aeneas exit $(python3 -c "import json;print(json.load(open('runs/A-$tag/receipt.json'))['exit'])")" >> runs/$tag.STATUS
  grep -c "" runs/A-$tag/stdout.log runs/A-$tag/stderr.log >> runs/$tag.STATUS
  grep -h "\[Error\]\|\[Warn" runs/A-$tag/stdout.log runs/A-$tag/stderr.log | cut -c1-400 | head -40 >> runs/$tag.STATUS
fi
echo DONE >> runs/$tag.STATUS
