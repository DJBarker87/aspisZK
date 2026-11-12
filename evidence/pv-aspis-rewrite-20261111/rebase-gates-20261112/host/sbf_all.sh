#!/bin/bash
# Runs INSIDE one capped scope. Usage: sbf_all.sh <tag> <src-dir-name> <cpu-list>
# Gate A of the rebase rerun: every program under programs/ with the recipe of the frozen build
# (evidence/future-version-20261111/host/fv_build_adapter_src.sh and fv_pool_build.sh: cargo-build-sbf
# 3.1.13, offline, locked, -j 4, clean environment, the same CARGO_* variables). One cargo target
# directory per tag and program, so the two trees are built independently (different source path,
# different target path, nothing reused between them).
# Feature names after the freeze (rename map fv_fz_rename_map.tsv): the deployed verifier is
# `--features aspis` (cmd.txt of the frozen build out/fz1); the two-transaction set
# `pool-adapter,private-leaf-salts` has no renamed feature.
# Builds: verifier with `aspis` and the devnet identifiers; verifier with the two-transaction set and
# the devnet identifiers; upload; pool; registry; aspis-verifier (legacy).
set -u
W=/home/dombarker/project-offloads/codex-pv-aspis-rewrite2-20261112
TAG=$1; S=$2; CPUS=$3
T=/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf
K=aspis
IDS=(ASPIS_R1_POOL_PROGRAM_ID=37hdATMkskKX1hiCWhz4nnzkD7GauYwX8EQwcpUDb3Zt ASPIS_R1_REGISTRY_PROGRAM_ID=9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q)
OUT=$W/out/$TAG; test ! -e $OUT/sbf || { echo "exists: $OUT/sbf"; exit 2; }
mkdir -p $OUT/sbf
( cd $W/$S && find crates programs docs tools/r1-cost-probe/src -name '*.rs' -o -name 'Cargo.toml' -o -name 'Cargo.lock' | sort | xargs sha256sum | sha256sum ) > $OUT/sbf/source_tree.sha256
# the formula of the frozen build's own source_tree.sha256 (out/fz1: 27e7316ab942...)
( cd $W/$S && find crates programs -name '*.rs' -o -name 'Cargo.toml' | sort | xargs sha256sum | sha256sum ) > $OUT/sbf/source_tree_frozen_formula.sha256
( cd $W/$S && sha256sum Cargo.lock Cargo.toml ) > $OUT/sbf/lock.sha256
$T --version > $OUT/sbf/tool_version.txt 2>&1
fail=0
one() { # name manifest-dir features ids(yes|no)
  local n=$1 m=$2 f=$3 ids=$4
  local O=$OUT/sbf/$n; mkdir -p $O
  local ENVV=(HOME=/home/dombarker USER=dombarker PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_HOME=/home/dombarker/.cargo
    CARGO_TARGET_DIR=$W/target/$TAG/sbf-$n CARGO_NET_OFFLINE=true "CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS=-C link-arg=--threads=4" CARGO_BUILD_JOBS=4)
  [ $ids = yes ] && ENVV+=("${IDS[@]}")
  local CMD=($T --manifest-path $W/$S/programs/$m/Cargo.toml --sbf-out-dir $O/artifacts)
  [ -n "$f" ] && CMD+=(--features $f)
  CMD+=(--skip-tools-install --offline -j 4 -- --locked)
  printf '%s\n' "${ENVV[@]}" > $O/env_exact.txt
  printf '%s\n' "${CMD[@]}" > $O/cmd.txt
  ( cd $W/$S && sha256sum Cargo.lock > $O/lock_before.txt
    /usr/bin/time -v -o $O/time.log taskset --cpu-list $CPUS env -i "${ENVV[@]}" "${CMD[@]}" > $O/stdout.log 2> $O/stderr.log; echo $? > $O/exit
    sha256sum Cargo.lock > $O/lock_after.txt )
  sha256sum $O/artifacts/*.so > $O/so.sha256 2>/dev/null
  ls -l $O/artifacts/*.so > $O/so.size 2>/dev/null
  # source files the compiler read for this program (cargo dep-info), relative to the source directory
  cat $W/target/$TAG/sbf-$n/sbpf-solana-solana/release/deps/*.d 2>/dev/null | tr ' ' '\n' | sed 's/:$//' | grep '\.rs$' | grep -v '/\.cargo/\|/rustc/\|platform-tools\|/\.cache/' | sed "s#^$W/$S/##" | sort -u > $O/dep_sources.txt
  echo "$n exit $(cat $O/exit) $(cut -d' ' -f1 $O/so.sha256 2>/dev/null | tr '\n' ' ')"
  [ "$(cat $O/exit)" = 0 ] || fail=1
}
one verifier-aspis r1-cost-probe $K yes
one verifier-twotx r1-cost-probe pool-adapter,private-leaf-salts yes
one upload aspis-upload "" no
one pool aspis-pool r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit no
one registry aspis-registry "" no
one aspis-verifier aspis-verifier "" no
( cd $OUT/sbf && for n in verifier-aspis verifier-twotx upload pool registry aspis-verifier; do for f in $n/artifacts/*.so; do [ -e $f ] && echo "$(sha256sum < $f | cut -d' ' -f1)  $(stat -c %s $f)  $f"; done; done ) > $OUT/sbf/TABLE.txt
cat $OUT/sbf/TABLE.txt
exit $fail
