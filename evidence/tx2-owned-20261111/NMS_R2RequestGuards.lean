import NMS_R2RequestBindings
import NMS_R2N_Interpreted
import NMS_R2N_RSLError
set_option autoImplicit false
noncomputable section
namespace NMS_R2RequestGuards
open Aeneas Aeneas.Std Result AdapterRw
open NMS_R2RequestBindings (Request)
open NMS_R2N_RSLScalars
attribute [local instance] Classical.propDecidable

def bad (q : Request) (devnet : Bool) : Bool :=
 decide (b32 q.verifier_profile ≠ RSL.PROFILE_BINDING) ||
 decide (b32 q.verifier_release ≠ RSL.RELEASE_BINDING) ||
 decide (b32 q.pool_program ≠ b32 (NHJ_IdPacket.pool devnet))

/-- Literal fixed key checks and deployed-ID read. The continuation is entered
only after all three checks; it has no required behavior on rejected inputs. -/
def actual {A : Type} (q : Request) (devnet : Bool)
 (next : RSL.Spec (core.result.Result A solana_program_error.ProgramError)) :=
 RSL.Spec.bind (NMS_R2N_Interpreted.liftResult
  (core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 q.verifier_profile r1_pool_adapter.PROFILE_BINDING)) fun p =>
 if p then RSL.Spec.pure (.Err .InvalidInstructionData) else
 RSL.Spec.bind (NMS_R2N_Interpreted.liftResult
  (core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 q.verifier_release r1_pool_adapter.RELEASE_BINDING)) fun r =>
 if r then RSL.Spec.pure (.Err .InvalidInstructionData) else
 RSL.Spec.bind (RSL.Spec.pure (NHJ_IdPacket.pool devnet)) fun program =>
 RSL.Spec.bind (NMS_R2N_Interpreted.liftResult
  (core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 q.pool_program program)) fun k =>
 if k then RSL.Spec.pure (.Err .InvalidInstructionData) else next

theorem source {A : Type} (q : Request) (devnet : Bool)
 (next : RSL.Spec (core.result.Result A solana_program_error.ProgramError)) :
 actual q devnet next = if bad q devnet then RSL.Spec.pure (.Err .InvalidInstructionData) else next := by
 unfold actual
 rw [NMS_R2RequestBindings.profile,NMS_R2RequestBindings.release]
 simp only [NMS_R2N_Interpreted.lift_ok,RSL.Spec.bind_pure]
 rw [NMS_R2RequestBindings.pool]
 simp only [NMS_R2N_Interpreted.lift_ok,RSL.Spec.bind_pure]
 unfold bad
 by_cases p : b32 q.verifier_profile ≠ RSL.PROFILE_BINDING <;>
  by_cases r : b32 q.verifier_release ≠ RSL.RELEASE_BINDING <;>
  by_cases k : b32 q.pool_program ≠ b32 (NHJ_IdPacket.pool devnet) <;> simp [p,r,k]

/-- Full guard observation transport, preserving the unexecuted suffix on
all error arms and keeping every observation of an entered continuation. -/
theorem full {A B : Type} (value : A → B) (q : Request) (devnet : Bool)
 (next : RSL.Spec (core.result.Result A solana_program_error.ProgramError)) (model : RSL.RS B)
 (law : NMS_R2N_Interpreted.Simulates (NMS_R2N_RSLError.reply value) next model) :
 NMS_R2N_Interpreted.Simulates (NMS_R2N_RSLError.reply value) (actual q devnet next)
  (RSL.RS.seq (RSL.RS.check (bad q devnet) .invalidInstructionData) model) := by
 rw [source]
 cases guard : bad q devnet with
 | false => simpa only [guard,Bool.false_eq_true,↓reduceIte,RSL.RS.check_false,RSL.RS.seq_pure] using law
 | true =>
   simp only [guard,Bool.true_eq,↓reduceIte,RSL.RS.check_true,RSL.RS.seq_throw]
   exact NMS_R2N_Interpreted.pure _ _
#print axioms source
#print axioms full
end NMS_R2RequestGuards
