import NIT_FinalCompleteness
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignFinal
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairComposition NIT_FieldInterpretation

theorem from_stream (parts powers : Parts) (sums : Nat → E) (logs : Nat → Final)
 (cuts : ∀ j,j<7 → cutFinal parts powers j (sums j) (logs j) (sums (j+1)))
 (muls : ∀ j,j<7 → EMul (logs j).mul_a (logs j).mul_b (logs j).product)
 (adds : ∀ j,j<7 → EAdd (logs j).add_a (logs j).add_b (logs j).reply)
 (fuel : Nat) (range : NHI_RangeProgress.Range)
 (last : range.end.val=7) (bound : range.start.val≤7) (enough : 7-range.start.val<fuel) :
 FinalTrace parts powers fuel (range,sums range.start.val) (sums 7) := by
 induction fuel generalizing range with
 | zero => omega
 | succ fuel ih =>
  by_cases active : range.start.val<7
  · obtain ⟨rest,next,inc,he⟩ := NHI_ForwardRange.active range (by omega)
    have tail := ih rest (by simpa only [he] using last) (by omega) (by omega)
    rw [inc] at tail
    exact .step fuel (range,sums range.start.val) (sums 7) (sums (range.start.val+1))
     (logs range.start.val) (cuts _ active) (muls _ active) (adds _ active) rest next tail
  · have atEnd : range.start.val=7 := by omega
    have done : FinalTrace parts powers (fuel+1) (range,sums range.start.val) (sums range.start.val) :=
     .done fuel _ (by change range.end.val≤range.start.val;omega)
    simpa only [atEnd] using done

theorem emitted (parts powers : Parts) (sums : Nat → E) (logs : Nat → Final)
 (cuts : ∀ j,j<7 → cutFinal parts powers j (sums j) (logs j) (sums (j+1)))
 (muls : ∀ j,j<7 → EMul (logs j).mul_a (logs j).mul_b (logs j).product)
 (adds : ∀ j,j<7 → EAdd (logs j).add_a (logs j).add_b (logs j).reply)
 (initial : sums 0=NHI_Scalar.zero) :
 FinalTrace parts powers 8 ({start:=0#usize,«end»:=7#usize},NHI_Scalar.zero) (sums 7) ∧
 FIo_Native.weights.Weights.pair_loop17 {start:=0#usize,«end»:=7#usize}
  parts powers NHI_Scalar.zero=ok (sums 7) := by
 have trace := from_stream parts powers sums logs cuts muls adds 8
  {start:=0#usize,«end»:=7#usize} rfl (by change (0:Nat)≤7;omega) (by change (7:Nat)-0<8;omega)
 change FinalTrace parts powers 8 (_,sums 0) _ at trace
 rw [initial] at trace
 exact ⟨trace,final_loop parts powers (sums 7) trace⟩

#print axioms from_stream
#print axioms emitted
end AspisR1.NIW_AlignFinal
