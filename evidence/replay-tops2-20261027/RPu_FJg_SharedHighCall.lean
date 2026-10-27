import RPu_FJg_PairProvenance
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJg_SharedHighCall
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NQ NE)
attribute [local irreducible] FIo_Native.weights.high_dot FIo_Native.weights.Weights.scalar_factor
/-- First high4 contraction in the SAME successful shared_high call. -/
theorem reached (self : FIo_Native.weights.Weights) (partials ap0 ap1 : Array NE 4#usize)
    (before after : Array NE 7#usize)
    (run : FIo_Native.weights.shared_high partials self ap0 ap1 before=ok (.Ok (),after)) :
    ∃ (row : Array (Array NQ 4#usize) 5#usize) (coeff : Array NQ 4#usize) (high : NE),
      Array.index_usize self.factors 0#usize=ok row ∧
      Array.index_usize row 4#usize=ok coeff ∧
      FIo_Native.weights.high_dot partials coeff=ok (.Ok high) := by
  unfold FIo_Native.weights.shared_high at run
  repeat' first
  | (solve | cases run)
  | uncase_result
  | head_reduce run
  | split at run
  exact ⟨_,_,_,by assumption,by assumption,by assumption⟩
#print axioms reached
end AspisR1.FJg_SharedHighCall
end
