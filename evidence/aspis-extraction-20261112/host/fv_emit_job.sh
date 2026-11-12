#!/bin/bash
# X7: the clean-emission check of one source tree, both on-chain programs. Runs INSIDE one fv_slot.sh scope
# (MemoryHigh 6G, MemoryMax 8G, no swap), started by fv_emit_candidate.sh. A tool record; nothing here is a proof.
# Usage: fv_emit_job.sh <tree name under W> <label>
# Steps (each timed with /usr/bin/time -v; one line per step in <run>/steps.tsv: name, exit, wall, peak RSS kB):
#   tools        tool and library hashes against the pinned values (stop on mismatch)
#   tree         cargo tree, both programs, host and SBF (resolved features)
#   emit-P       one Charon run and one Aeneas -abort-on-error run of program P (fv_emit_run.py)
#   native-P     the raw output compiled against the native library with zero edits (fv_emit_native.sh), errors listed
#   gates        (i) bodiless, (ii) completeness, (iii) reversed mutable iterator (name scan) and (iii') by type,
#                (iv) write route (name scan) and (iv') by type, (v) read before write and write order, (vi) boundary
#                grammar (planted negatives first), (vii) target_os, (viii) branch- and call-following read after write;
#                planted controls of the scans (crate, dependency, the privacy lead's control2)
#   tables, shared-function comparison, constants, MANIFEST.json
set -u
W=/home/dombarker/project-offloads/future-version-20261111
B=$(cd $(dirname $0) && pwd)
S=$W/$1; L=$2; O=$W/x7/runs/$L; TG=$W/x7/target/$L
CV=$B/fv_emit_cfg_verifier.json; CP=$B/fv_emit_cfg_pool.json
PLANT_M=$W/x1b/runs/probe-m/runs/C/out.llbc     # X1b's control crate x1b_probe_m (reversed mutable iterator)
PLANT_W=$W/x1/runs/rw2b/runs/C/out.llbc         # X1's rw2b emission (lifecycle handlers borrow mutably)
test -d $S || { echo "no tree $S"; exit 2; }
PHASE=${PHASE:-all}   # all, or post: gates, tables, comparison, constants and manifest on an existing run (a new scope)
if [ $PHASE = all ]; then
  test ! -e $O/steps.tsv || { echo "exists: $O"; exit 2; }
  mkdir -p $O/gates $TG
  printf 'step\texit\twall\tpeak_rss_kb\n' > $O/steps.tsv
else
  test -e $O/steps.tsv || { echo "no run at $O"; exit 2; }
  printf 'post-phase\t-\t%s\t-\n' "$(date -u +%FT%TZ)" >> $O/steps.tsv
fi
st() {  # st <name> <cmd...>: run, log to steps/<name>.log, record exit, wall, peak
  local n=$1; shift; mkdir -p $O/steps
  /usr/bin/time -v -o $O/steps/$n.time "$@" > $O/steps/$n.log 2>&1; local rc=$?
  printf '%s\t%s\t%s\t%s\n' $n $rc "$(grep Elapsed $O/steps/$n.time | awk '{print $NF}')" "$(grep 'Maximum resident' $O/steps/$n.time | awk '{print $NF}')" >> $O/steps.tsv
  return $rc
}
# ---- tools and library
tools() {
  local C=/home/dombarker/project-offloads/codex-pc-prov-p4x-20261110/PCWH_T004_out/bin LIB=$W/x3/aeneas-src/backends/lean ok=0
  while read -r f want; do
    got=$(sha256sum $f | cut -d' ' -f1); [ "$got" = "$want" ] && v=pass || { v=FAIL; ok=1; }
    printf '%s\t%s\t%s\t%s\n' $f $got $want $v
  done <<EOT
$C/charon 57aa2359bb3e9a84480f7e4802dcdc700ef05709de30ec0eb97581b3f9c5f851
$C/charon-driver 6a6552bce70d59e041fb96a67c08294377ef16d3f77a7876fea7f1250ee37845
$C/aeneas 230ee9f0c4902ea3415a01960f6887e2d4c71bc82e8b4e78dfac398da657df91
$LIB/lean-toolchain 414acabc0b69c985a83eb7015af2317f0df08f7513779d512945456f8eedfdd9
$LIB/lake-manifest.json 12fb593d2fe949112f0db995ea6648dd0a8521ed1951005839942ab084eb3364
$LIB/lakefile.lean 784d5c0d761f6d4d246c03483b60a9dd9d9a926b0c0bcba448aff4e6daf5ffac
EOT
  return $ok
}
if [ $PHASE = all ]; then
tools > $O/tools.tsv 2>&1; rc=$?
printf 'tools\t%s\t-\t-\n' $rc >> $O/steps.tsv
[ $rc -eq 0 ] || { echo "tool or library hash mismatch"; cat $O/tools.tsv; exit 3; }
st tree bash $B/fv_emit_tree.sh $S $O/tree $TG
for P in verifier pool; do
  CF=$B/fv_emit_cfg_$P.json; NS=$(python3 -c "import json,sys;print(json.load(open(sys.argv[1]))['ns'])" $CF)
  st emit-$P python3 -I $B/fv_emit_run.py $CF $S $O/$P $TG/charon
  R=$O/$P/aeneas/raw/$NS
  if [ -f $R/Funs.lean ]; then
    st native-$P bash $B/fv_emit_native.sh $R $NS $O/$P/native
    python3 -I $B/fv_emit_errs.py $O/$P/native $NS > $O/$P/native-errors.tsv
  else
    echo "no Funs.lean for $P" >> $O/steps.tsv
  fi
done
fi
# ---- gates (each prints a final 'gate (..) ...: pass|FAIL' line)
rm -f $O/gates/*.txt   # a post phase regenerates every gate output
for P in verifier pool; do
  CF=$B/fv_emit_cfg_$P.json; NS=$(python3 -c "import json,sys;print(json.load(open(sys.argv[1]))['ns'])" $CF); R=$O/$P/aeneas/raw/$NS
  st g1-$P sh -c "python3 -I $B/fv_emit_bodiless.py $R $CF > $O/gates/i-bodiless-$P.txt"
  st g2-$P sh -c "python3 -I $B/fv_emit_complete.py $O/$P/charon/out.llbc $R $CF > $O/gates/ii-complete-$P.txt"
  st g5-$P sh -c "python3 -I $B/fv_emit_gate_writeorder.py $CF $R > $O/gates/v-writeorder-$P.txt"
done
sha256sum $PLANT_M $PLANT_W > $O/gates/planted-llbc.sha256
st g3 sh -c "python3 -I $B/fv_emit_gate_mutiter.py $PLANT_M $S $O/gates/iii verifier=$O/verifier/charon/out.llbc,programs/r1-cost-probe,crates/aspis-r1-cost-probe,crates/aspis-statement,crates/aspis-core pool=$O/pool/charon/out.llbc,programs/aspis-pool,crates/aspis-statement,crates/aspis-core > $O/gates/iii-mutiter-both.txt"
st g4 sh -c "python3 -I $B/fv_emit_gate_writeroute.py $PLANT_W $S $O $O/gates/iv $CV $CP > $O/gates/iv-writeroute-both.txt"
st g6 sh -c "bash $B/fv_emit_gate_grammar.sh $S > $O/gates/vi-grammar-both.txt"
st g3t sh -c "for P in verifier pool; do python3 -I $B/fv_emit_gate_types.py iter $O/\$P/charon/out.llbc aspis_; done > $O/gates/iii-t-types-both.txt"
st g4t sh -c "python3 -I $B/fv_emit_gate_types.py state $O/verifier/charon/out.llbc aspis_ write_zero_data,write_lamports > $O/gates/iv-t-types-both.txt; python3 -I $B/fv_emit_gate_types.py state $O/pool/charon/out.llbc aspis_ write_account_data_v1 >> $O/gates/iv-t-types-both.txt"
st plant sh -c "bash $B/fv_emit_plant.sh $O/gates/plant > $O/gates/plant-table.txt"
st g8 sh -c "bash $B/fv_emit_gate_raw.sh $O $CV $CP > $O/gates/viii-raw-both.txt"
st g7 sh -c "python3 -I $B/fv_emit_gate_targetos.py $S $O $CV $CP > $O/gates/vii-targetos-both.txt"
# ---- tables, comparison, constants, manifest
st tables-verifier python3 -I $B/fv_emit_tables.py $CV $S $O
st tables-pool python3 -I $B/fv_emit_tables.py $CP $S $O
st shared sh -c "python3 -I $B/fv_emit_shared.py $S $O $CV $CP > $O/shared.tsv"
for P in verifier pool; do   # against the worker's own final emission (the config's reference_raw), for attribution
  CF=$B/fv_emit_cfg_$P.json
  read NS REF < <(python3 -c "import json,sys;c=json.load(open(sys.argv[1]));print(c['ns'], c['reference_raw'])" $CF)
  st bodycmp-$P sh -c "python3 -I $B/fv_emit_bodycmp.py $O/$P/aeneas/raw/$NS $REF > $O/$P/compare-reference.tsv"
done
[ "${SKIP_CONSTEVAL:-0}" = 1 ] || st consteval python3 -I $B/fv_emit_consteval.py $S $O $CV $TG/charon   # needs the Charon target dir
grep -h '^gate ' $O/gates/*.txt > $O/gates.txt
st manifest python3 -I $B/fv_emit_manifest.py $S $O $CV $CP
du -sh $TG > $O/target-size.txt 2>&1
[ "${KEEP_TARGET:-0}" = 1 ] || rm -rf $TG
cat $O/steps.tsv; cat $O/gates.txt
! grep -q ': FAIL' $O/gates.txt
