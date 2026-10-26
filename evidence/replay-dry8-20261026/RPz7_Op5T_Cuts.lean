import RPz7_Op5T_Accepted
set_option autoImplicit false
noncomputable section
namespace AspisR1.Op5T_Cuts
open Aeneas Aeneas.Std Result

/-- Invert only the actual current TX1 successful suffix, stopping at batch0.
The Prepared and scratch are those returned by the original preparation. -/
theorem first_batch (ops : AspisR1CurrentCaller.Ops) {Hash : Type}
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash)
    (pub proof : Slice U8) (split : Usize) (hash : Hash)
    (p : AspisR1CurrentCaller.verifier.Prepared)
    (g : Array AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact 29#usize)
    (saved : alloc.vec.Vec U8)
    (success : AspisR1CurrentCaller.Tx1Reachability.afterPrepare ops D pub proof split hash none p g = ok (.Ok saved)) :
    ∃ folded, ops.op6 D proof p folded 0#usize hash = ok (.Ok ()) := by
  unfold AspisR1CurrentCaller.Tx1Reachability.afterPrepare at success
  repeat' first
  | (solve | exact ⟨_,by assumption⟩)
  | (solve | cases success)
  | uncase_result
  | head_reduce success
  | split at success

/-- Same authenticated TX2 body: its own batch1 is required before query1. -/
theorem second_batch (ops : VTop_Stages.Ops) {Hash : Type}
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub proof checkpoint : Slice U8)
    (success : VTop_Stages.verifier.candidate.tx2_common ops D pub proof checkpoint hash none = ok (.Ok ())) :
    ∃ p folded, ops.op5 D proof p folded 1#usize hash = ok (.Ok ()) := by
  rw [← Tx2I_Cuts.common_source ops D hash pub proof checkpoint none] at success
  unfold Tx2I_Cuts.common at success
  repeat' first
  | (solve | exact ⟨_,_,by assumption⟩)
  | (solve | cases success)
  | uncase_result
  | head_reduce success
  | split at success

#print axioms first_batch
#print axioms second_batch
end AspisR1.Op5T_Cuts
end
