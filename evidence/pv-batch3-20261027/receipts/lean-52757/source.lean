import PV_B3_CanonicalCarrier
import PV_B3_FieldScalar
import R1Z.ProverRwP7CurrentBaseBridge
import R1Z.ProverCommitM31Ops48
noncomputable section
namespace PV_B3_Canonical
open Aeneas Aeneas.Std Result PV_B3_FieldTransport
set_option autoImplicit false
 theorem current_sub (x y : U32) (hx : M x) (hy : M y) : ∃ z,
    PV_B3_Copy_117.aspis_core.field.M31.sub x y = ok z ∧ M z := by
  change ∃ z, PV_B3_FieldScalar.N.sub x y = ok z ∧ M z
  rw [PV_B3_FieldScalar.sub]
  change ∃ z, R1Z.ProverRwP7CurrentBaseBridge.S.sub x y = ok z ∧ M z
  rw [R1Z.ProverRwP7CurrentBaseBridge.sub]
  obtain ⟨z,hz,hc,_⟩ := R1Z.ProverCommitM31Ops48.sub_exact x y hx hy
  exact ⟨z,hz,hc⟩
#print axioms current_sub
end PV_B3_Canonical
