import NMX_R2_CheckpointCarrier
import NMX_R2_ResultRelation
import NMX_R2_Observation
set_option autoImplicit false
namespace NMX_R2_CheckpointAfter
open Aeneas Aeneas.Std Result AdapterRw NMX_R2_Carrier
abbrev PE := solana_program_error.ProgramError
/-- Fold only the question-mark tail; the arbitrary Result is consumed here,
never retained as a premise of the parent root. -/
theorem member (r : Result (core.result.Result Usize PE)) (env : RSL.Env) :
 RSL.RS.bind (NMX_R2_ResultRelation.rust r)
  (fun n => RSL.RS.ofExcept (reply id (NMX_R2_CheckpointTail.tail n))) env
  (NMX_R2_ObserveResult.observe id (NMX_R2_CheckpointTail.after r)) := by
 have actual : NMX_R2_ObserveResult.observe id (NMX_R2_CheckpointTail.after r) =
   NMX_R2_Observation.rustBind (NMX_R2_ObserveResult.observe id r)
    (fun n => NMX_R2_ObserveResult.observe id (.ok (NMX_R2_CheckpointTail.tail n))) := by
   cases r with
   | fail e => rfl
   | div => rfl
   | ok reply => cases reply <;> rfl
 rw [actual]
 apply NMX_R2_Observation.rust_sound (NMX_R2_ObserveResult.observe id r)
  (fun n => NMX_R2_ObserveResult.observe id (.ok (NMX_R2_CheckpointTail.tail n)))
  (NMX_R2_ResultRelation.rust r)
  (fun n => RSL.RS.ofExcept (reply id (NMX_R2_CheckpointTail.tail n))) env
 · rfl
 · intro n
   rfl
#print axioms member
end NMX_R2_CheckpointAfter
