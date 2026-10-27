import FJg_SharedHighCall
import FIp_ArraySetValue
import FJc_ArrayUpdateValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJg_SharedHighTrace
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NQ NE)
attribute [local irreducible] FIo_Native.weights.high_dot FIo_Native.weights.Weights.scalar_factor
/-- SAME shared_high success: original high/low factors and the part1 write,
including its frame under the later absorption write. -/
theorem reached (self : FIo_Native.weights.Weights) (partials ap0 ap1 : Array NE 4#usize)
    (before after : Array NE 7#usize)
    (run : FIo_Native.weights.shared_high partials self ap0 ap1 before=ok (.Ok (),after)) :
    ∃ (row : Array (Array NQ 4#usize) 5#usize) (highCoeffs low0 low1 : Array NQ 4#usize)
      (high s0 s1 scale value old absorption : NE) (back : NE → Array NE 7#usize),
      Array.index_usize self.factors 0#usize=ok row ∧
      Array.index_usize row 4#usize=ok highCoeffs ∧
      FIo_Native.weights.high_dot partials highCoeffs=ok (.Ok high) ∧
      Array.index_usize row 0#usize=ok low0 ∧
      FIo_Native.weights.Weights.scalar_factor low0 ap0=ok s0 ∧
      Array.index_usize row 1#usize=ok low1 ∧
      FIo_Native.weights.Weights.scalar_factor low1 ap1=ok s1 ∧
      FIo_Native.aspis_core.field.wide_exact.WideExact.mul s0 s1=ok scale ∧
      FIo_Native.aspis_core.field.wide_exact.WideExact.mul scale high=ok value ∧
      Array.index_mut_usize before 1#usize=ok (old,back) ∧
      Array.update (back value) 3#usize absorption=ok after := by
  unfold FIo_Native.weights.shared_high at run
  repeat' first
  | (solve | cases run)
  | uncase_result
  | head_reduce run
  | split at run
  cases Result.ok.inj run
  exact ⟨_,_,_,_,_,_,_,_,_,_,_,_,by assumption,by assumption,by assumption,
    by assumption,by assumption,by assumption,by assumption,by assumption,
    by assumption,by assumption,by assumption⟩

/-- Exact part1 value after the shared body; no assumption on prior parts. -/
theorem written (before after : Array NE 7#usize) (value old absorption : NE)
    (back : NE → Array NE 7#usize)
    (hb : Array.index_mut_usize before 1#usize=ok (old,back))
    (hu : Array.update (back value) 3#usize absorption=ok after) :
    FIp_ArrayValue.value after 1=AspisR1CurrentWide.Proof.decodeWide (FIo_FieldBridge.wide value) := by
  have eb := FIp_ArraySetValue.back before 1#usize old back hb
  rw [FJc_ArrayUpdateValue.value (back value) after 3#usize absorption 1 hu,
    if_neg (by decide),eb]
  simpa only [show (1#usize).val=1 from by decide] using FIp_ArraySetValue.same before 1#usize value (by decide)
#print axioms reached
#print axioms written
end AspisR1.FJg_SharedHighTrace
end
