import R1Z.PV_Canon_Inverse
import R1Z.ProverCommitInterpolationInverse48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result
 theorem interpolation_inverse_canonical (x y : U32)
    (h : AspisR1ProducerRelease47.inverse_ref x = .ok y) : M y := by
  apply inverse_owned_canonical x y
  rw [← ProverCommitInterpolationInverse48.source_inverse]
  exact h
#print axioms interpolation_inverse_canonical
end R1Z.PV_Canon
