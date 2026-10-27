import PV_B3_PolynomialEmission
import PV_B3_Result
namespace PV_B3_PolynomialCounter
open Aeneas Aeneas.Std Result ControlFlow PV_B3_Result PV_B3_Copy_117
set_option autoImplicit false
abbrev Q := aspis_core.field.QM31
abbrev State := Q × Usize
 def Progress (i : Usize) : ControlFlow State Q → Prop
 | .done _ => True
 | .cont s => s.2 = Usize.wrapping_sub i 1#usize
 theorem body_counter (poly : Array Q 28#usize) (powers : Array Q 3#usize)
    (p : host_arithmetic.PreparedQm31Multiplier) (a : Q) (i : Usize) :
    Safe (Progress i) (host_arithmetic.evaluate_state_only_polynomial_loop.body poly powers p a i) := by
  unfold host_arithmetic.evaluate_state_only_polynomial_loop.body
  simp only [lift,bind_tc_ok]
  split
  · apply bind_any
    intro q
    apply bind_any
    intro block_value
    apply bind_any
    intro accumulator
    intro cf h
    cases h
    rfl
  · intro cf h
    cases h
    trivial
#print axioms Progress
#print axioms body_counter
end PV_B3_PolynomialCounter
