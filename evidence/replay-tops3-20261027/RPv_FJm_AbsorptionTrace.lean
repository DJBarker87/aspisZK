import RPu_FJg_SharedHighTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJm_AbsorptionTrace
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NQ NE)
attribute [local irreducible] FIo_Native.weights.high_dot FIo_Native.weights.Weights.scalar_factor

/-- Second contraction of the actual shared body, ending in the slot3 write. -/
theorem reached (w : FIo_Native.weights.Weights) (partials ap0 ap1 : Array NE 4#usize)
    (before after : Array NE 7#usize)
    (run : FIo_Native.weights.shared_high partials w ap0 ap1 before=ok (.Ok (),after)) :
    ∃ (row : Array (Array NQ 4#usize) 5#usize) (coeff low0 low1 : Array NQ 4#usize)
      (high s0 s1 scale value : NE) (base : Array NE 7#usize),
      Array.index_usize w.factors 2#usize=ok row ∧
      Array.index_usize row 4#usize=ok coeff ∧
      FIo_Native.weights.high_dot partials coeff=ok (.Ok high) ∧
      Array.index_usize row 0#usize=ok low0 ∧
      FIo_Native.weights.Weights.scalar_factor low0 ap0=ok s0 ∧
      Array.index_usize row 1#usize=ok low1 ∧
      FIo_Native.weights.Weights.scalar_factor low1 ap1=ok s1 ∧
      FIo_Native.aspis_core.field.wide_exact.WideExact.mul s0 s1=ok scale ∧
      FIo_Native.aspis_core.field.wide_exact.WideExact.mul scale high=ok value ∧
      Array.update base 3#usize value=ok after := by
  unfold FIo_Native.weights.shared_high at run
  repeat' first | (solve | cases run) | uncase_result | head_reduce run | split at run
  cases Result.ok.inj run
  exact ⟨_,_,_,_,_,_,_,_,_,_,by assumption,by assumption,by assumption,by assumption,
    by assumption,by assumption,by assumption,by assumption,by assumption,by assumption⟩
#print axioms reached
end AspisR1.FJm_AbsorptionTrace
end
