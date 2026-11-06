import NIT_LowChain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignLow
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_LowChain NIT_FieldInterpretation

theorem from_stream (ap0 ap1 : Powers)
 (cells : Nat → LowCells) (logs : Nat → Low)
 (cuts : ∀ j,j<16 → cutLow ap0 ap1 j (cells j) (logs j) (cells (j+1)))
 (laws : ∀ j,j<16 → EMul (logs j).a (logs j).b (logs j).product)
 (scales : ∀ j,j<16 → NIT_LowInterpretation.Scale (logs j).scale_a (logs j).scaled)
 (fuel : Nat) (range : NHI_RangeProgress.Range)
 (last : range.end.val=16) (bound : range.start.val≤16) (enough : 16-range.start.val<fuel) :
 Trace ap0 ap1 fuel (range,cells range.start.val) (cells 16) := by
 induction fuel generalizing range with
 | zero => omega
 | succ fuel ih =>
  by_cases active : range.start.val<16
  · have cut := cuts range.start.val active
    have law := laws range.start.val active
    have scale := scales range.start.val active
    obtain ⟨rest,_,next,he,inc,_⟩ := NIT_LowStep.step ap0 ap1
     (range,cells range.start.val) (cells (range.start.val+1)) (logs range.start.val) cut law scale last
    change rest.start.val=range.start.val+1 at inc
    have tail := ih rest he (by omega) (by omega)
    rw [inc] at tail
    exact .step fuel (range,cells range.start.val) (cells 16)
     (cells (range.start.val+1)) (logs range.start.val) last cut law scale rest next tail
  · have atEnd : range.start.val=16 := by omega
    have done : Trace ap0 ap1 (fuel+1) (range,cells range.start.val) (cells range.start.val) :=
     .done fuel _ (by change range.end.val≤range.start.val;omega)
    simpa only [atEnd] using done

theorem emitted (ap0 ap1 : Powers) (cells : Nat → LowCells) (logs : Nat → Low)
 (cuts : ∀ j,j<16 → cutLow ap0 ap1 j (cells j) (logs j) (cells (j+1)))
 (laws : ∀ j,j<16 → EMul (logs j).a (logs j).b (logs j).product)
 (scales : ∀ j,j<16 → NIT_LowInterpretation.Scale (logs j).scale_a (logs j).scaled) :
 Trace ap0 ap1 17 ({start:=0#usize,«end»:=16#usize},cells 0) (cells 16) ∧
 FIo_Native.weights.Weights.pair_loop15 {start:=0#usize,«end»:=16#usize} ap0 ap1 (cells 0)=ok (cells 16) := by
 have trace := from_stream ap0 ap1 cells logs cuts laws scales 17
  {start:=0#usize,«end»:=16#usize} rfl (by change (0:Nat)≤16;omega) (by change (16:Nat)-0<17;omega)
 refine ⟨trace,?_⟩
 rw [NIG_LowLoop.low_source]
 exact interpreted ap0 ap1 17 _ _ trace

#print axioms from_stream
#print axioms emitted
end AspisR1.NIW_AlignLow
