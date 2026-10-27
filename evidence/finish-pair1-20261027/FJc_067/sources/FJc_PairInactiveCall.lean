import FJc_SharedSelf
import FJc_LowValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJc_PairInactiveCall
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE)
/-- Original two-fold Pair reaches the inactive contraction on its OWN
powers, low array and final-message bytes, including the shared-high path. -/
theorem reached [FIo_Native.Allocation] (self : FIo_Native.weights.Weights)
    (alpha : Slice NE) (f : Slice U8) (kappa out : NE)
    (folds : Slice.len alpha=2#usize)
    (run : FIo_Native.weights.Weights.pair self alpha f kappa=ok (.Ok out)) :
    ∃ (a0 a1 : NE) (ap0 ap1 : Array NE 4#usize) (low : Array NE 16#usize) (inactive : NE),
      Slice.index_usize alpha 0#usize=ok a0 ∧
      FIo_Native.weights.powers 4#usize a0=ok ap0 ∧
      Slice.index_usize alpha 1#usize=ok a1 ∧
      FIo_Native.weights.powers 4#usize a1=ok ap1 ∧
      FIo_Native.weights.Weights.pair_loop15 {start:=0#usize,«end»:=16#usize} ap0 ap1
        (Array.repeat 16#usize FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO)=ok low ∧
      FIo_Native.weights.grouped_inactive_pair self f low=ok inactive := by
  unfold FIo_Native.weights.Weights.pair at run
  simp only [folds,ite_true,show ¬(2#usize=1#usize) from by decide,ite_false] at run
  repeat' first
  | (solve | cases run)
  | uncase_result
  | head_reduce run
  | split at run
  all_goals
    try
      have same := FJc_SharedSelf.value self _ _ _ _ (by assumption)
      subst_vars
    obtain ⟨a0,h0⟩ : ∃ a0,Slice.index_usize alpha 0#usize=ok a0 := ⟨_,by assumption⟩
    obtain ⟨a1,h1⟩ : ∃ a1,Slice.index_usize alpha 1#usize=ok a1 := ⟨_,by assumption⟩
    obtain ⟨ap0,hp0⟩ : ∃ ap0,FIo_Native.weights.powers 4#usize a0=ok ap0 := ⟨_,by assumption⟩
    obtain ⟨ap1,hp1⟩ : ∃ ap1,FIo_Native.weights.powers 4#usize a1=ok ap1 := ⟨_,by assumption⟩
    obtain ⟨low,hl⟩ : ∃ low,FIo_Native.weights.Weights.pair_loop15
      {start:=0#usize,«end»:=16#usize} ap0 ap1
      (Array.repeat 16#usize FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO)=ok low := ⟨_,by assumption⟩
    obtain ⟨inactive,hi⟩ : ∃ inactive,FIo_Native.weights.grouped_inactive_pair self f low=ok inactive := ⟨_,by assumption⟩
    exact ⟨a0,a1,ap0,ap1,low,inactive,h0,hp0,h1,hp1,hl,hi⟩
#print axioms reached
end AspisR1.FJc_PairInactiveCall
end
