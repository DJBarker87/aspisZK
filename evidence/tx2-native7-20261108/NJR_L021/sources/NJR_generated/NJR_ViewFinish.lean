import NJR_FinishInstall
import NJJ_Common
import MultiproofConeSlices
set_option autoImplicit false
noncomputable section
namespace NJR_ViewFinish
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2

def empty : Slice U8 := ⟨[],by simp⟩
/-- Literal View at candidate.rs:313--321 of the frozen revision, using the
pinned checked-slice model. Proof contents are not a caller-supplied View. -/
def view (proof : Slice U8) (inactive : aspis_core.field.wide_exact.WideExact) : verifier.View where
 variant:=.S2
 semantic:=empty
 y1:=empty
 inactive:=inactive
 round0:=MultiproofConeSlices.sub proof 7527#usize 7751#usize
 folded_root:=none
 round1:=MultiproofConeSlices.sub proof 7783#usize 8007#usize
 final_message:=MultiproofConeSlices.sub proof 8007#usize 10055#usize
 query_bytes:=empty

/-- The actual source suffix, with its checked range operations left in place.
This helper's finish argument is an auxiliary congruence parameter; it is not
an admissible positive-root hypothesis. -/
def suffix (finish : NJJ_Common.Finish) (proof : Slice U8)
 (p : verifier.Prepared) (a : verifier.Accumulator)
 (inactive : aspis_core.field.wide_exact.WideExact) := do
 let round0 ← core.slice.index.Slice.index
  (core.slice.index.SliceIndexRangeUsizeSlice U8) proof {start:=7527#usize,«end»:=7751#usize}
 let round1 ← core.slice.index.Slice.index
  (core.slice.index.SliceIndexRangeUsizeSlice U8) proof {start:=7783#usize,«end»:=8007#usize}
 let final ← core.slice.index.Slice.index
  (core.slice.index.SliceIndexRangeUsizeSlice U8) proof {start:=8007#usize,«end»:=10055#usize}
 finish {variant:=.S2,semantic:=empty,y1:=empty,inactive:=inactive,round0:=round0,folded_root:=none,
  round1:=round1,final_message:=final,query_bytes:=empty} p a none

theorem ranges (finish : NJJ_Common.Finish) (proof : Slice U8)
 (p : verifier.Prepared) (a : verifier.Accumulator)
 (inactive : aspis_core.field.wide_exact.WideExact) (length : proof.val.length=57607) :
 suffix finish proof p a inactive=finish (view proof inactive) p a none := by
 unfold suffix
 rw [MultiproofConeSlices.range_total proof 7527#usize 7751#usize (by change 7527≤7751;omega) (by change 7751≤proof.val.length;omega)]
 rw [bind_tc_ok]
 rw [MultiproofConeSlices.range_total proof 7783#usize 8007#usize (by change 7783≤8007;omega) (by change 8007≤proof.val.length;omega)]
 rw [bind_tc_ok]
 rw [MultiproofConeSlices.range_total proof 8007#usize 10055#usize (by change 8007≤10055;omega) (by change 10055≤proof.val.length;omega)]
 rfl

/-- Actual primitive windows are consequences of literal source construction,
with no external View-equality premise. -/
theorem windows (proof : Slice U8) (inactive : aspis_core.field.wide_exact.WideExact) :
 (view proof inactive).round0.val=(proof.val.drop 7527).take 224 ∧
 (view proof inactive).round1.val=(proof.val.drop 7783).take 224 ∧
 (view proof inactive).final_message.val=(proof.val.drop 8007).take 2048 := ⟨rfl,rfl,rfl⟩

#print axioms ranges
#print axioms windows
end NJR_ViewFinish
