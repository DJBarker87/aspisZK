import PV_B3_PolynomialCounter
import PV_B3_LinearsRank
namespace PV_B3_PolynomialRank
open Aeneas Aeneas.Std Result ControlFlow PV_B3_Result PV_B3_Copy_117 PV_B3_PolynomialCounter
set_option autoImplicit false
 def rank (s : State) : Nat := s.2.val
 theorem decreases (poly : Array Q 28#usize) (powers : Array Q 3#usize)
    (p : host_arithmetic.PreparedQm31Multiplier) (a : Q) (i : Usize) (next : State)
    (h : host_arithmetic.evaluate_state_only_polynomial_loop.body poly powers p a i = ok (cont next)) :
    rank next < rank (a,i) := by
  have hc := body_counter poly powers p a i (cont next) h
  change next.2 = Usize.wrapping_sub i 1#usize at hc
  have hi : 0<i.val := by
    unfold host_arithmetic.evaluate_state_only_polynomial_loop.body at h
    split at h
    · assumption
    · cases h
  unfold rank
  dsimp only
  rw [hc,PV_B3_LinearsRank.decrement i hi]
  omega
#print axioms rank
#print axioms decreases
end PV_B3_PolynomialRank
