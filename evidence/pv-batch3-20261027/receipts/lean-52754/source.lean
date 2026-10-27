import PV_B3_CanonicalCarrier
import PV_B3_FieldScalar
import R1Z.ProverRwP7CurrentBaseBridge
import R1Z.ProverCommitM31Ops48
noncomputable section
namespace PV_B3_Canonical
open Aeneas Aeneas.Std Result PV_B3_FieldTransport
set_option autoImplicit false
 theorem mul (x y : U32) : ∃ z,
    PV_B3_Copy_117.aspis_core.field.M31.mul x y = ok z ∧ M z := by
  rw [PV_B3_FieldScalar.mul]
  change ∃ z, R1Z.ProverRwP7CurrentBaseBridge.S.mul x y = ok z ∧ M z
  rw [R1Z.ProverRwP7CurrentBaseBridge.mul]
  obtain ⟨z,hz,hc,_⟩ := R1Z.ProverCommitM31Ops48.mul_exact x y
  exact ⟨z,hz,hc⟩
#print axioms mul
end PV_B3_Canonical
