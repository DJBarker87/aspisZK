import PV_L1E_Source_070
import PV_L1D_CallbackSafe
import PV_L1E_SafeObserve
set_option autoImplicit false
noncomputable section
namespace PV_L1E_QuerySafety
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1D_Logged PV_L1D_CallbackSafe
variable [ExternalTypes] [ExternalFuns]
theorem safe_coe {α : Type} (r : Result α) : Safe (r : Logged α) := rfl
#print axioms safe_coe
theorem safe_PV_L1D_QueryAbsorb
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (self : host_transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8) :
  Safe (PV_L1D_QueryAbsorb.produce aspis_coredigestDigest32Inst self row payload) := by
  unfold PV_L1D_QueryAbsorb.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | with_reducible exact safe_lift _
    | with_reducible exact safe_coe _
    | with_reducible exact safe_pure _
    | with_reducible exact PV_L1E_SafeObserve.phase _ _ _ (by intro h; cases h)
    | with_reducible apply safe_bind
    | intro value
    | split <;> try simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1D_QueryAbsorb
end PV_L1E_QuerySafety
