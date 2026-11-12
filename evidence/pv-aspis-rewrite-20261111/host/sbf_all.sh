#!/bin/bash
# Runs INSIDE one capped scope. Usage: sbf_all.sh <tag> [<src-dir-name>]
# Gate A: every program under programs/ with the recipe of docs/r1/BUILD.md (cargo-build-sbf 3.1.13,
# platform-tools v1.52, offline, locked, -j 4, taskset 0-3, clean environment). One cargo target
# directory per program build, shared between tags, so a later tag recompiles only what changed;
# the source directory path is the same for every tag.
# Builds: verifier with the branch-head feature set and the devnet identifiers (K); verifier with
# the pinned feature set and the devnet identifiers (pin2); upload; pool; registry; aspis-verifier.
set -u
W=/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111
TAG=$1; S=${2:-src}
T=/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf
K=pool-adapter,future-one-tx-lean,private-leaf-salts,future-fast-kmul,future-fast-prepared,future-fast-square,future-validated-decode,future-merkle-single-pass,future-tight-base,future-tight-weights,future-lazy-boundary,future-d-inactive-tensor,future-d-pair-expansion,future-merkle-in-place,future-lazy-horner,future-fold-shared
IDS=(ASPIS_R1_POOL_PROGRAM_ID=37hdATMkskKX1hiCWhz4nnzkD7GauYwX8EQwcpUDb3Zt ASPIS_R1_REGISTRY_PROGRAM_ID=9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q)
OUT=$W/out/$TAG; test ! -e $OUT/sbf || { echo "exists: $OUT/sbf"; exit 2; }
mkdir -p $OUT/sbf
( cd $W/$S && find crates programs docs tools/r1-cost-probe/src -name '*.rs' -o -name 'Cargo.toml' -o -name 'Cargo.lock' | sort | xargs sha256sum | sha256sum ) > $OUT/sbf/source_tree.sha256
fail=0
one() { # name manifest-dir features ids(yes|no)
  local n=$1 m=$2 f=$3 ids=$4
  local O=$OUT/sbf/$n; mkdir -p $O
  local ENVV=(HOME=/home/dombarker USER=dombarker PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_HOME=/home/dombarker/.cargo
    CARGO_TARGET_DIR=$W/target/sbf-$n CARGO_NET_OFFLINE=true "CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS=-C link-arg=--threads=4" CARGO_BUILD_JOBS=4)
  [ $ids = yes ] && ENVV+=("${IDS[@]}")
  local CMD=($T --manifest-path $W/$S/programs/$m/Cargo.toml --sbf-out-dir $O/artifacts)
  [ -n "$f" ] && CMD+=(--features $f)
  CMD+=(--skip-tools-install --offline -j 4 -- --locked)
  printf '%s\n' "${ENVV[@]}" > $O/env_exact.txt
  printf '%s\n' "${CMD[@]}" > $O/cmd.txt
  ( cd $W/$S && sha256sum Cargo.lock > $O/lock_before.txt
    /usr/bin/time -v -o $O/time.log taskset --cpu-list 0-3 env -i "${ENVV[@]}" "${CMD[@]}" > $O/stdout.log 2> $O/stderr.log; echo $? > $O/exit
    sha256sum Cargo.lock > $O/lock_after.txt )
  sha256sum $O/artifacts/*.so > $O/so.sha256 2>/dev/null
  ls -l $O/artifacts/*.so > $O/so.size 2>/dev/null
  echo "$n exit $(cat $O/exit) $(cut -d' ' -f1 $O/so.sha256 2>/dev/null | tr '\n' ' ')"
  [ "$(cat $O/exit)" = 0 ] || fail=1
}
one verifier-K r1-cost-probe $K yes
one verifier-pin2 r1-cost-probe pool-adapter,private-leaf-salts yes
one upload aspis-upload "" no
one pool aspis-pool r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit no
one registry aspis-registry "" no
one aspis-verifier aspis-verifier "" no
( cd $OUT/sbf && for n in verifier-K verifier-pin2 upload pool registry aspis-verifier; do for f in $n/artifacts/*.so; do [ -e $f ] && echo "$(sha256sum < $f | cut -d' ' -f1)  $(stat -c %s $f)  $f"; done; done ) > $OUT/sbf/TABLE.txt
cat $OUT/sbf/TABLE.txt
exit $fail
