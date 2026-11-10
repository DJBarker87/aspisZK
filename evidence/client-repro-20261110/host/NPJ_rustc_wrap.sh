#!/bin/bash
# NPJ_ path-equivalence wrapper: maps this workspace onto the original NDZ paths
# inside rustc only, without entering RUSTFLAGS (which cargo hashes into -C metadata).
W=/home/dombarker/project-offloads/codex-cx-client-20261110
O=/home/dombarker/project-offloads/codex-cx-devnet-rehearse-20261029
RUSTC="$1"; shift
exec "$RUSTC" "$@" "--remap-path-prefix=$W/NDZ_src=$O/NDZ_src" "--remap-path-prefix=$W/target-$NPJ_N=$O/NDZ_native-target"
