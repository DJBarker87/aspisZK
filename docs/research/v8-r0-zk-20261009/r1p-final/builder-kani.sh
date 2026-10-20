#!/bin/sh
# Host-only proof compilation / bounded equivalence, not arithmetic execution.
set -eu
R=/home/dombarker/project-offloads/codex-cx-builder-ref2-20261021
case "${1:-}" in
  transport) W="$R/gates-source"; H=s2_row_equals_d18; set -- --manifest-path tools/r1-builder-reference/Cargo.toml ;;
  records-parametric) W="$R/source"; H=records_equal_parametric_roots; set -- -Z stubbing -p aspis-statement --lib ;;
  records) W="$R/source"; H=records_equal_copied_reference; set -- -Z stubbing -p aspis-statement --lib ;;
  *) exit 64 ;;
esac
E="$R/kani-$H"
mkdir -p "$E"
[ ! -e "$E/kani.log" ] || exit 65
python3 - <<'PY'
from pathlib import Path
v=0
for p in Path('/sys/fs/cgroup').rglob('memory.max'):
    try:
        s=p.read_text().strip()
        if s != 'max' and (p.parent/'cgroup.procs').read_text().strip(): v+=int(s)
    except OSError: pass
print('populated MemoryMax bytes',v,'requested',8*2**30,flush=True)
assert v+8*2**30 <=55*2**30, 'host reservation exceeds 55 GiB'
PY
cd "$W"
export PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_BUILD_JOBS=4
cargo kani --version > "$E/tool-version.txt"
systemd-run --user --scope --quiet -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 \
    /usr/bin/time -v -o "$E/time.log" timeout 600 \
    cargo kani "$@" -j 4 --output-format terse --harness "$H" > "$E/kani.log" 2>&1
