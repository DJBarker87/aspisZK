#!/bin/bash
# X7: the SBF builds of both programs of one source tree, with the FULL build log kept, for the stack-offset
# comparison. Runs INSIDE one fv_slot.sh scope. The recipes are the lead's W/fv_frz_build.sh (verifier program:
# features aspis, the given pool and registry ids) and W/fv_pool_build.sh (Pool: the deployed feature list), copied
# here with two changes only: the output directory is under W/x7/runs/<label>/sbf, and the cargo target directory is
# a NEW directory under W/x7/target per build (W/fv_pool_build.sh names its target directory after the tree only, and
# W/target/sbf-pool-src-frz-a already holds a finished build of the frozen tree: reusing it would recompile nothing
# and print no compiler message). Each target directory is deleted after its build (disk).
# Usage: fv_emit_sbf.sh <tree name> <label> [<pool id> <registry id>]
#   defaults: pool 37hdATMkskKX1hiCWhz4nnzkD7GauYwX8EQwcpUDb3Zt, registry 9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q
#   (the arguments of evidence/future-version-20261111/host/fv_frz_build.sh's measurement builds)
# Time is expected in compilation (two SBF builds, a few minutes each on four cores).
set -u
W=/home/dombarker/project-offloads/future-version-20261111
S=$1; L=$2; POOL=${3:-37hdATMkskKX1hiCWhz4nnzkD7GauYwX8EQwcpUDb3Zt}; REG=${4:-9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q}
T=/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf
B=$(cd $(dirname $0) && pwd)
O=$W/x7/runs/$L/sbf; mkdir -p $O
rc_all=0
for P in verifier pool; do
  OUT=$O/$P; TD=$W/x7/target/sbf-$L-$P
  test ! -e $OUT/build.log || { echo "exists: $OUT"; exit 2; }
  mkdir -p $OUT; rm -rf $TD
  if [ $P = verifier ]; then
    ENVV=(HOME=/home/dombarker USER=dombarker PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_HOME=/home/dombarker/.cargo
      CARGO_TARGET_DIR=$TD CARGO_NET_OFFLINE=true "CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS=-C link-arg=--threads=4" CARGO_BUILD_JOBS=4
      ASPIS_R1_POOL_PROGRAM_ID=$POOL ASPIS_R1_REGISTRY_PROGRAM_ID=$REG)
    CMD=($T --manifest-path $W/$S/programs/r1-cost-probe/Cargo.toml --sbf-out-dir $OUT/artifacts --features aspis --skip-tools-install --offline -j 4 -- --locked)
  else
    ENVV=(HOME=/home/dombarker USER=dombarker PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_HOME=/home/dombarker/.cargo
      CARGO_TARGET_DIR=$TD CARGO_NET_OFFLINE=true "CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS=-C link-arg=--threads=4" CARGO_BUILD_JOBS=4)
    CMD=($T --manifest-path $W/$S/programs/aspis-pool/Cargo.toml --sbf-out-dir $OUT/artifacts --features r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit --skip-tools-install --offline -j 4 -- --locked)
  fi
  printf '%s\n' "${ENVV[@]}" > $OUT/env_exact.txt
  printf '%s\n' "${CMD[@]}" > $OUT/cmd.txt
  ( cd $W/$S && find crates programs -name '*.rs' -o -name 'Cargo.toml' | sort | xargs sha256sum | sha256sum ) > $OUT/source_tree.sha256
  $T --version > $OUT/tool_version.txt 2>&1
  ( cd $W/$S && /usr/bin/time -v -o $OUT/build.time taskset --cpu-list 0-3 env -i "${ENVV[@]}" "${CMD[@]}" ) > $OUT/build.log 2>&1
  rc=$?; echo $rc > $OUT/exit
  sha256sum $OUT/artifacts/*.so > $OUT/so.sha256 2>/dev/null
  grep -a 'Stack offset' $OUT/build.log > $OUT/stack.txt
  echo "$P exit $rc stack-messages $(wc -l < $OUT/stack.txt) $(cat $OUT/so.sha256 2>/dev/null)"
  du -sh $TD > $OUT/target-size.txt 2>/dev/null; rm -rf $TD
  [ $rc -eq 0 ] || rc_all=$rc
done
python3 -I $B/fv_emit_elfids.py $O/verifier/artifacts/aspis_r1_cost_probe_program.so $POOL $REG > $O/verifier/elf-ids.txt 2>&1
exit $rc_all
