import NHU_ExpandPacket
import RPv_FJa_ExpandValue
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.NIH_ExpandOuter
open FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode)
open pool_v1.pair_forest_copy_terminal
/-- One stage equation derived from the retained ACTUAL emitted loop. -/
theorem stage {N : Usize} (iter : core.slice.iter.Iter NQ)
 (weights : Array NQ N) (len : Usize) :
 Selectors.expand_loop0 iter weights len=(do
  let (o,next)←core.slice.iter.IteratorSliceIter.next iter
  match o with
  | none=>ok weights
  | some coordinate=>do
    let p←field.PreparedQm31Multiplier.new coordinate
    let after←Selectors.expand_loop0_loop0
      (FJa_ReverseStep.cursor len) weights p
    let nextlen←len*2#usize
    Selectors.expand_loop0 next after nextlen) := by
 rw [Selectors.expand_loop0.eq_def]
 rfl
/-- The original native stage has the next invariant on the SAME iterator suffix,
weights, coordinate and prepared owner; existing inner and outer induction reused. -/
theorem result {N : Usize} (iter : core.slice.iter.Iter NQ)
 (weights : Array NQ N) (len : Usize) (level : Nat)
 (size : len.val=2^level)
 (cap : 2^(level+(iter.slice.val.drop iter.i).length)≤N.val)
 (canonical : FIw_ArrayValue.canonical weights)
 (coordinates : ∀ x∈iter.slice.val,Canon x) :
 ∃ out,Selectors.expand_loop0 iter weights len=ok out ∧
 FIw_ArrayValue.canonical out ∧
 FIv_NativeArray.value out=FJa_ExpandModel.value
  ((iter.slice.val.drop iter.i).map decode) len.val (FIv_NativeArray.value weights) := by
 obtain ⟨out,run,canon⟩:=JFy_SelectorOuter.source (iter.slice.val.drop iter.i)
   iter weights len level rfl size cap canonical (by
     intro x member
     exact coordinates x (List.mem_of_mem_drop member))
 exact ⟨out,run,canon,FJa_ExpandValue.loop iter weights out len coordinates canonical run⟩
#print axioms stage
#print axioms result
end AspisR1.NIH_ExpandOuter
end
