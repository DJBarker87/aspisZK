import PV_B3_PolynomialEmission
namespace PV_B3_PolynomialStop
open Aeneas Aeneas.Std Result ControlFlow PV_B3_Copy_117
set_option autoImplicit false
 theorem body_done (poly : Array aspis_core.field.QM31 28#usize)
    (powers : Array aspis_core.field.QM31 3#usize)
    (p : host_arithmetic.PreparedQm31Multiplier) (a : aspis_core.field.QM31) :
    host_arithmetic.evaluate_state_only_polynomial_loop.body poly powers p a 0#usize = ok (done a) := by
  unfold host_arithmetic.evaluate_state_only_polynomial_loop.body
  rw [if_neg (by decide)]
 theorem loop_done (poly : Array aspis_core.field.QM31 28#usize)
    (powers : Array aspis_core.field.QM31 3#usize)
    (p : host_arithmetic.PreparedQm31Multiplier) (a : aspis_core.field.QM31) :
    host_arithmetic.evaluate_state_only_polynomial_loop poly powers p a 0#usize = ok a := by
  unfold host_arithmetic.evaluate_state_only_polynomial_loop
  rw [loop.eq_def]
  dsimp only
  rw [body_done]
#print axioms body_done
#print axioms loop_done
end PV_B3_PolynomialStop
