#!/bin/bash
# Optimisation rounds, profiling pass. Usage: fv_opt_prof.sh <tree> (a copy of src-xp1, e.g. src-opt-prof)
# 1. debug-line build of the X1 source (stripped output must equal X1);
# 2. phase-marker build (cu-profiling, detail-phases), a separate ELF, never measured as a candidate;
# 3. one_tx_worst built with LiteSVM register tracing (own target directory);
# 4. traced run of the rollover withdrawal (N = 255, seed 60) with the debug ELF, and a marker run
#    of the phase build; 5. trace attribution with fv_profile.py.
# Time is expected in compilation (two SBF builds of about a minute, one cold native tool build),
# then one fixture proof per run (tens of seconds) and the trace attribution (minutes).
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
S=$1
K=pool-adapter,future-one-tx-lean,private-leaf-salts,future-fast-kmul,future-fast-prepared,future-fast-square,future-validated-decode,future-merkle-single-pass,future-tight-base,future-tight-weights,future-lazy-boundary,future-d-inactive-tensor,future-d-pair-expansion,future-merkle-in-place,future-lazy-horner,future-fold-shared
D=$W/OPT_prof.done; rm -f $D
mkdir -p opt
bash fv_slot.sh OPT-dbg-x1 3000 bash $W/fv_opt_dbg.sh OPT-dbg-x1 $K $S || { echo DBG_BUILD_FAILED > $D; exit 1; }
echo "dbg stripped: $(cut -d' ' -f1 out/OPT-dbg-x1/so.sha256)  X1: $(cut -d' ' -f1 out/X1-rewrites/so.sha256)" >> $D
bash fv_slot.sh OPT-prof-x1 3000 bash $W/fv_build_adapter_src.sh OPT-prof-x1 $K,cu-profiling,detail-phases $S || { echo PROF_BUILD_FAILED >> $D; exit 1; }
B=$W/opt/one_tx_worst-trace
if [ ! -x $B ]; then
  cp $W/one_tx_worst.rs $W/$S/tools/r1-cost-probe/src/bin/one_tx_worst.rs
  sed -i 's/^litesvm = "=0.16.0"$/litesvm = { version = "=0.16.0", features = ["register-tracing"] }/' $W/$S/tools/r1-cost-probe/Cargo.toml
  grep -n '^litesvm' $W/$S/tools/r1-cost-probe/Cargo.toml >> $D
  bash fv_slot.sh OPT-trace-tool 3000 bash -c "cd $W/$S/tools/r1-cost-probe && taskset --cpu-list 0-3 env -i HOME=/home/dombarker USER=dombarker PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_HOME=/home/dombarker/.cargo CARGO_TARGET_DIR=$W/target/native-trace-$S CARGO_NET_OFFLINE=true CARGO_BUILD_JOBS=4 cargo +1.94.1 build --release --offline --bin one_tx_worst && cp $W/target/native-trace-$S/release/one_tx_worst $B" || { echo TOOL_BUILD_FAILED >> $D; exit 1; }
fi
TD=$W/traces/OPT-x1-worst
test ! -e $TD || { echo "trace dir exists" >> $D; exit 1; }
mkdir -p $TD
bash fv_slot.sh OPT-trace-run 3000 bash -c "SBF_TRACE_DIR=$TD ASPIS_SOURCE_REVISION=\$(cat $W/SOURCE_REVISION)+$S taskset --cpu-list 0-3 $B $W/devnet/PIN2_TRANSACTIONS.json $W/devnet/pool.so $W/opt/prof-trace.json withdrawal:255:60:basic X1dbg=$W/out/OPT-dbg-x1/artifacts/aspis_r1_cost_probe_program.so" || { echo TRACE_RUN_FAILED >> $D; exit 1; }
bash fv_slot.sh OPT-phase-run 3000 bash -c "ASPIS_SOURCE_REVISION=\$(cat $W/SOURCE_REVISION)+$S taskset --cpu-list 0-3 $B $W/devnet/PIN2_TRANSACTIONS.json $W/devnet/pool.so $W/opt/prof-phases.json withdrawal:255:60:full,transfer:255:60:basic Xprof=$W/out/OPT-prof-x1/artifacts/aspis_r1_cost_probe_program.so X1=$W/out/X1-rewrites/artifacts/aspis_r1_cost_probe_program.so" || { echo PHASE_RUN_FAILED >> $D; exit 1; }
ls -la $TD > $W/opt/prof-trace-files.txt
for f in $TD/*.program_id; do echo "$(basename $f .program_id) $(cat $f) $(stat -c %s ${f%.program_id}.regs)"; done >> $W/opt/prof-trace-files.txt
VID=$(python3 -c "import json;print(json.load(open('$W/devnet/PIN2_TRANSACTIONS.json'))['programs']['verifier'])")
REGS=$(for f in $TD/*.program_id; do if [ "$(cat $f)" = "$VID" ]; then echo ${f%.program_id}.regs; fi; done | head -1)
CU=$(python3 -c "import json;r=json.load(open('$W/opt/prof-trace.json'))['results'][0]['elfs'][0]['runs'][0];print(r['verifier_cu'])")
echo "verifier regs $REGS cu $CU" >> $D
bash fv_slot.sh OPT-trace-profile 3000 python3 $W/fv_profile.py $W/out/OPT-dbg-x1/linked-unstripped.so $REGS $CU $W/opt/prof-x1-worst-verifier.json || { echo PROFILE_FAILED >> $D; exit 1; }
rm -f $TD/*.trace $TD/*.insns
echo DONE >> $D
