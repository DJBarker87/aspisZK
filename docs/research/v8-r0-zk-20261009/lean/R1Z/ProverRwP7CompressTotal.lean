import R1Z.ProverRwP7CompressFiniteTotal
import R1Z.ProverRwP7CompressPrimitives
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP7CompressTotal
open Aeneas Aeneas.Std Result ProverRwFull ProverRwDictionaryTower
variable [ExternalTypes]
-- This closes the owned reference's primitive/read/termination obligations.
-- It is not a shipped/reference equality or an op223 installation.
theorem total (ops : ExternalFuns) (tag : U32) (values : Slice aspis_core.field.M31)
    (lambda : aspis_core.field.QM31) :
    letI : ExternalFuns := ProverRwP6BodyStore.selected ops
    ∃ out, ProverRwP6CompressSource.compress tag values lambda = ok out := by
  letI : ExternalFuns := ProverRwP6BodyStore.selected ops
  rw [ProverRwP6CompressControl.compress_finite]
  have hc : aspis_core.field.CM31.from_m31 tag =
      ok (fromC ⟨tag,AspisR1ProducerRelease47.field.M31.ZERO⟩) := rfl
  have hq : aspis_core.field.QM31.from_cm31 (fromC ⟨tag,AspisR1ProducerRelease47.field.M31.ZERO⟩) =
      ok (fromQ ⟨⟨tag,AspisR1ProducerRelease47.field.M31.ZERO⟩,AspisR1ProducerRelease47.field.CM31.ZERO⟩) := rfl
  simp only [hc,hq,bind_tc_ok]
  apply ProverRwP7CompressFiniteTotal.finite_total
  · change 0+_=_
    omega
  · exact ProverRwP7CompressPrimitives.scale ops
  · exact ProverRwP7CompressPrimitives.add ops
  · exact ProverRwP7CompressPrimitives.mul ops
#print axioms total
end R1Z.ProverRwP7CompressTotal
