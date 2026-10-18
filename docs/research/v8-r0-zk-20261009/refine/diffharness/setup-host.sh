#!/bin/sh
# setup-host.sh <scratch-dir> <prod-tarball> <writers-dir> <diffharness-dir>
# Builds the scratch workspace: exported production tree (read-only source of truth),
# the scratch-only shims of shim.patch.txt, the writer copies and this harness as a member.
set -eu
D=$1; TAR=$2; W=$3; H=$4
rm -rf "$D"; mkdir -p "$D"
tar -xf "$TAR" -C "$D"
python3 - "$D" "$H/shim.patch.txt" <<'PY'
import sys, re
d, patch = sys.argv[1], open(sys.argv[2]).read()
parts = re.split(r'^--- append to (\S+)\n', patch, flags=re.M)
for i in range(1, len(parts), 2):
    path, text = parts[i], parts[i + 1]
    with open(d + '/' + path, 'a') as f:
        f.write('\n' + text)
cargo = open(d + '/Cargo.toml').read()
cargo = cargo.replace('members = [\n', 'members = [\n    "refine/writers",\n    "refine/diffharness",\n', 1)
open(d + '/Cargo.toml', 'w').write(cargo)
PY
mkdir -p "$D/refine"
cp -r "$W" "$D/refine/writers"; cp -r "$H" "$D/refine/diffharness"
sed -i '/^\[workspace\]$/d' "$D/refine/writers/Cargo.toml"
