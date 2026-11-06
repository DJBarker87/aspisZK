import NIT_CommonChain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignCommon
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_CommonChain NIT_FieldInterpretation

/-- The supplied cells/logs are the chronological native stream. The proof
never selects a fresh local log or a fresh post-array from model evaluation. -/
theorem from_stream (w : W) (hf : NHI_TensorOuterStep.Factors w)
 (cells : Nat → CommonCells) (logs : Nat → Common)
 (cuts : ∀ j,j<16 → cutCommon (row2 w) (row3 w) j (cells j) (logs j) (cells (j+1)))
 (laws : ∀ j,j<16 → QMul (logs j).lhs (logs j).rhs (logs j).reply)
 (fuel : Nat) (range : NHI_RangeProgress.Range)
 (last : range.end.val=16) (bound : range.start.val≤16) (enough : 16-range.start.val<fuel) :
 Trace w fuel (range,cells range.start.val) (w,cells 16) := by
 induction fuel generalizing range with
 | zero => omega
 | succ fuel ih =>
  by_cases active : range.start.val<16
  · have cut := cuts range.start.val active
    have law := laws range.start.val active
    obtain ⟨rest,_,next,he,inc⟩ := NIT_CommonInterpretation.step w hf
     (range,cells range.start.val) (cells (range.start.val+1)) (logs range.start.val) cut law last
    change rest.start.val=range.start.val+1 at inc
    have tail := ih rest he (by omega) (by omega)
    rw [inc] at tail
    exact .step fuel (range,cells range.start.val) (w,cells 16)
     (cells (range.start.val+1)) (logs range.start.val) last cut law rest next tail
  · have atEnd : range.start.val=16 := by omega
    have done : Trace w (fuel+1) (range,cells range.start.val) (w,cells range.start.val) :=
     .done fuel _ (by change range.end.val≤range.start.val;omega)
    simpa only [atEnd] using done

/-- All sixteen observed cuts fold to the exact emitted Common call, on the
same final cells; this is native-stream-to-witness, not model-to-log existence. -/
theorem emitted (w : W) (hf : NHI_TensorOuterStep.Factors w)
 (cells : Nat → CommonCells) (logs : Nat → Common)
 (cuts : ∀ j,j<16 → cutCommon (row2 w) (row3 w) j (cells j) (logs j) (cells (j+1)))
 (laws : ∀ j,j<16 → QMul (logs j).lhs (logs j).rhs (logs j).reply) :
 Trace w 17 ({start:=0#usize,«end»:=16#usize},cells 0) (w,cells 16) ∧
 FIo_Native.weights.Weights.pair_loop1 {start:=0#usize,«end»:=16#usize} w (cells 0)=ok (w,cells 16) := by
 have trace := from_stream w hf cells logs cuts laws 17
  {start:=0#usize,«end»:=16#usize} rfl (by change (0:Nat)≤16;omega) (by change (16:Nat)-0<17;omega)
 refine ⟨trace,?_⟩
 rw [NIG_CommonLoop.common_source]
 exact interpreted w hf 17 _ _ trace

#print axioms from_stream
#print axioms emitted
end AspisR1.NIW_AlignCommon
