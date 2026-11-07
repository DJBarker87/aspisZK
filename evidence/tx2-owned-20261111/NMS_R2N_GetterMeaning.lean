import NMS_R2N_GeneralGetters
import NMS_R2N_ObservationMaps
import NMS_R2N_RSLPoolCarriers
set_option autoImplicit false
noncomputable section
namespace NMS_R2N_GetterMeaning
open Aeneas Aeneas.Std Result AdapterRw
variable {M : Type → Type} [Monad M]
/-- Fresh E003 getter with only its std clone operation interpreted. -/
def get (clone : solana_program_error.ProgramError → M solana_program_error.ProgramError)
 (a : r1_pool_adapter.owned.OwnedAccount) : M (core.result.Result (Slice U8) solana_program_error.ProgramError) :=
 match a.bytes with
 | .Ok stored => pure (.Ok stored.deref)
 | .Err error => do
   let copied ← clone error
   pure (.Err copied)

def clone (error : solana_program_error.ProgramError) : RSL.Spec solana_program_error.ProgramError :=
 RSL.Spec.map NMS_R2N_RSLError.raw (NMS_R2N_CloneReference.clone (NMS_R2N_RSLError.error error))

def meaning (a : r1_pool_adapter.owned.OwnedAccount) := get clone a

theorem erases (ops : Ops) (a : r1_pool_adapter.owned.OwnedAccount) :
 get ops.op35 a = NMS_Emitted.get ops a := by
 cases h : a.bytes <;> rfl

/-- All ProgramError variants, including a stopped String clone, are now
transported to the corrected reference. No snapshot-error restriction or
allocation-success premise is needed. Std/allocator interpretation is retained. -/
theorem full (a : r1_pool_adapter.owned.OwnedAccount) :
 NMS_R2N_Interpreted.Simulates (NMS_R2N_RSLError.reply NMS_R2N_RSLScalars.bytes)
  (meaning a) (NMS_R2N_GeneralGetters.data (NMS_R2N_RSLPoolCarriers.account a)) := by
 unfold meaning get NMS_R2N_GeneralGetters.data NMS_R2N_GeneralGetters.get
 dsimp only [NMS_R2N_RSLPoolCarriers.account]
 cases stored : a.bytes with
 | Ok bytes =>
   exact NMS_R2N_Interpreted.pure _ _
 | Err error =>
   apply NMS_R2N_Interpreted.bind NMS_R2N_RSLError.error (NMS_R2N_RSLError.reply NMS_R2N_RSLScalars.bytes)
   · exact NMS_R2N_ObservationMaps.cancel NMS_R2N_RSLError.raw NMS_R2N_RSLError.error NMS_R2N_RSLError.right _
   · intro copied
     exact NMS_R2N_Interpreted.pure _ _
#print axioms erases
#print axioms full
end NMS_R2N_GetterMeaning
