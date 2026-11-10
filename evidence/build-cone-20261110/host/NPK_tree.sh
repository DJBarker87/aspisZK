#!/bin/bash
# NPK_ cargo tree / cargo metadata with the platform-tools cargo (1.89.0-sbpf-solana-v1.52), deployed features.
set -u
W=/home/dombarker/project-offloads/codex-cx-cone-20261110; OUT=$W/out/NPK_T001; mkdir -p $OUT
ENVV=(HOME=/home/dombarker USER=dombarker PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_HOME=/home/dombarker/.cargo
  RUSTUP_TOOLCHAIN=1.89.0-sbpf-solana-v1.52 CARGO_NET_OFFLINE=true CARGO_TARGET_DIR=$W/target/NPK_T001)
rc=0
t(){ name=$1; src=$2; prog=$3; feat=$4
  cd $W/$src
  env -i "${ENVV[@]}" cargo tree -e normal --target sbpf-solana-solana --manifest-path programs/$prog/Cargo.toml --features $feat --locked --offline -f '{p} {f}' > $OUT/tree_$name.txt 2> $OUT/tree_$name.err || rc=1
  env -i "${ENVV[@]}" cargo tree -e normal,build --target sbpf-solana-solana --manifest-path programs/$prog/Cargo.toml --features $feat --locked --offline -f '{p} {f}' > $OUT/tree_build_$name.txt 2>> $OUT/tree_$name.err || rc=1
  env -i "${ENVV[@]}" cargo metadata --format-version 1 --filter-platform sbpf-solana-solana --manifest-path programs/$prog/Cargo.toml --features $feat --locked --offline > $OUT/metadata_$name.json 2> $OUT/metadata_$name.err || rc=1
}
t verifier src-v r1-cost-probe pool-adapter,private-leaf-salts
t pool src-p aspis-pool r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit
exit $rc
