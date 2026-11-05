import NHY_RegistrySlots
import NHY_RegistryPrimitives
import NHY_PolicyModel
set_option autoImplicit false
noncomputable section
namespace NHY_RegistryPipeline
open Aeneas Aeneas.Std Result
open AdapterRw.aspis_statement.pool_v1.verifier_registry

def bindHelpers {E : Type} (missing : AspisR1.IDa_Deployed.Uninstalled E) :=
 {missing with adapter := NHY_RegistrySlots.install missing.adapter}

def configuration {E : Type} (missing : AspisR1.IDa_Deployed.Uninstalled E)
    (devnet : Bool) (indexError : E) (reservation : AspisR1.NP6_StdModel.Reservation) :=
 NHJ_DeployedIds.configuration (NHY_PolicyModel.bindPolicy (bindHelpers missing)) devnet indexError reservation

theorem paused_v1 {E : Type} (missing : AspisR1.IDa_Deployed.Uninstalled E)
    (devnet : Bool) (indexError : E) (reservation : AspisR1.NP6_StdModel.Reservation) (r : VerifierRegistryV1) :
    (configuration missing devnet indexError reservation).adapter.op25 r =
      NHY_RegistryReference.flag_ref r.flags 1#u8 := rfl

theorem immutable_v1 {E : Type} (missing : AspisR1.IDa_Deployed.Uninstalled E)
    (devnet : Bool) (indexError : E) (reservation : AspisR1.NP6_StdModel.Reservation) (r : VerifierRegistryV1) :
    (configuration missing devnet indexError reservation).adapter.op26 r =
      NHY_RegistryReference.flag_ref r.flags 2#u8 := rfl

theorem paused_v2 {E : Type} (missing : AspisR1.IDa_Deployed.Uninstalled E)
    (devnet : Bool) (indexError : E) (reservation : AspisR1.NP6_StdModel.Reservation) (r : VerifierRegistryV2) :
    (configuration missing devnet indexError reservation).adapter.op27 r =
      NHY_RegistryReference.flag_ref r.flags 1#u8 := rfl

theorem immutable_v2 {E : Type} (missing : AspisR1.IDa_Deployed.Uninstalled E)
    (devnet : Bool) (indexError : E) (reservation : AspisR1.NP6_StdModel.Reservation) (r : VerifierRegistryV2) :
    (configuration missing devnet indexError reservation).adapter.op28 r =
      NHY_RegistryReference.flag_ref r.flags 2#u8 := rfl

theorem policy {E : Type} (missing : AspisR1.IDa_Deployed.Uninstalled E)
    (devnet : Bool) (indexError : E) (reservation : AspisR1.NP6_StdModel.Reservation) :
    (configuration missing devnet indexError reservation).adapter.op15 = NHY_PolicyModel.policy := rfl

def expectedStatus (v : U8) : core.result.Result VerifierEntryStatusV1 PoolV1VerifierRegistryFormatError :=
 if v=0#u8 then .Ok .Pending else if v=1#u8 then .Ok .Active
 else if v=2#u8 then .Ok .Paused else if v=3#u8 then .Ok .Retired else .Err .InvalidStatus

/-- Compose the retained per-constructor/error proofs into the complete carrier
expected by the native TryFrom harness, on every input byte. -/
theorem status (v : U8) : NHY_RegistryPrimitives.status v = ok (expectedStatus v) := by
  by_cases h0 : v=0#u8
  · subst v; exact NHY_RegistryPrimitives.pending
  · by_cases h1 : v=1#u8
    · subst v; exact NHY_RegistryPrimitives.active
    · by_cases h2 : v=2#u8
      · subst v; exact NHY_RegistryPrimitives.paused
      · by_cases h3 : v=3#u8
        · subst v; exact NHY_RegistryPrimitives.retired
        · rw [NHY_RegistryPrimitives.invalid v h0 h1 h2 h3]
          simp only [expectedStatus,h0,h1,h2,h3,if_false]

#print axioms paused_v1
#print axioms immutable_v1
#print axioms paused_v2
#print axioms immutable_v2
#print axioms policy
#print axioms status
end NHY_RegistryPipeline
