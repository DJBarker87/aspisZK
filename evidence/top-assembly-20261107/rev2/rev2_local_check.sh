#!/bin/sh
# Clean local replay for the RSL Revision 2 impact check and TAS_TopB.
# Run from evidence/rowspec-lead-20261107.  Single files, `lake env lean -o`,
# dependency order, development machine (every file far below 8 GiB).
# Phase A: RSL rev2 + TCK/TAS/TFM/EVB.  Phase B: every merged NMV_/NNE_ module
# whose import closure is local, UNPATCHED.  Phase C: the three NMV no-write
# modules with NMV_REV2_NOWRITE.patch applied, plus their dependants.
# Phase D: TAS_Rev2Support, TAS_TopB and TAS_TopB_NNE.
set -u
T=../top-assembly-20261107/rev2
OUT=$T/REV2_LOCAL_COMPILE.tsv
AX=$T/REV2_LOCAL_AXIOMS.txt
rm -rf .lake/build .lake/stage
mkdir -p .lake/stage .lake/build/lib/lean .lake/patched
printf 'phase\tmodule\texit\twall_s\tpeak_rss_bytes\tswaps\tsha256\n' > $OUT
: > $AX
one() { # phase module source
  cp "$3" ".lake/stage/$2.lean"
  out=$( { /usr/bin/time -l lake env lean -o ".lake/build/lib/lean/$2.olean" ".lake/stage/$2.lean" ; } 2>&1 )
  rc=$?
  wall=$(printf '%s\n' "$out" | awk '/ real /{print $1}')
  rss=$(printf '%s\n' "$out" | awk '/maximum resident set size/{print $1}')
  sw=$(printf '%s\n' "$out" | awk '/ swaps$/{print $1}')
  printf '%s\t%s\texit=%s\t%s\t%s\t%s\t%s\n' "$1" "$2" "$rc" "$wall" "$rss" "$sw" \
    "$(shasum -a 256 .lake/stage/$2.lean | cut -d' ' -f1)" >> $OUT
  printf '%s\n' "$out" | grep -E "depends on|does not depend|error" | sed "s/^/[$1 $2] /" | head -40 >> $AX
}
for f in RSL_Base RSL_Pool RSL_TX2_217 RSL_TX2_234 RSL_TX2_233 RSL_TX2_242 RSL_TX2_241 RSL_TX2_240 \
         RSL_TX2_221 RSL_TX2_213 RSL_Verifier RSL_TX1_136 RSL_TX1_137 RSL_TX1_087 RSL_TX1_094 \
         RSL_TX1_328 RSL_TX1_345 RSL_TX1_344 RSL_TX1_333 RSL_TX1_330; do one A $f $f.lean; done
one A TCK_WeakRoot0 ../top-check-20261107/TCK_WeakRoot0.lean
one A TAS_Interfaces ../top-assembly-20261107/TAS_Interfaces.lean
one A TAS_Top ../top-assembly-20261107/TAS_Top.lean
one A TFM_TopExact ../top-form-20261107/TFM_TopExact.lean
one A EVB_EventB ../event-b-20261107/EVB_EventB.lean
SW=../stage-wrap-20261111; PA=../phys-adapter-20261111
for m in NMV_RslLaws NMV_RslSnapshots NMV_RslDomain NMV_RslFold NMV_WindowEval NMV_WindowClock \
         NMV_WindowStage NMV_G2 NMV_SdkFrame NMV_G2State NMV_WindowRoots NMV_SdkExec NMV_SnapshotExec \
         NMV_CopyExec NMV_ConcreteWindows NMV_NoWrite NMV_NoWriteSdk NMV_NoWritePool; do one B $m $SW/$m.lean; done
for m in NMV_FullState NMV_WeakFold NMV_PhysicalCarrier NMV_Stage1Frame; do one B $m $SW/$m.lean; done
for m in NNE_AcceptedCuts NNE_RslOk NNE_SelectedRoutes NNE_SelectedContext; do one B $m $PA/$m.lean; done
# Phase C: patched copies (the merged files themselves are not edited).
for m in NMV_NoWritePool NMV_NoWriteOwned NMV_NoWrite241; do cp $SW/$m.lean .lake/patched/; done
( cd .lake/patched && patch -s -p3 < ../../$T/NMV_REV2_NOWRITE.patch )
for m in NMV_NoWritePool NMV_NoWriteOwned NMV_NoWrite241; do one C $m .lake/patched/$m.lean; done
for m in NMV_G2Reference NMV_TasRoots NMV_CandidateRoots; do one C $m $SW/$m.lean; done
one D TAS_Rev2Support $T/TAS_Rev2Support.lean
one D TAS_TopB ../top-assembly-20261107/TAS_TopB.lean
one D TAS_TopB_NNE ../top-assembly-20261107/TAS_TopB_NNE.lean
cat $OUT
grep -c sorryAx $AX
