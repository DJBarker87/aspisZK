import PV_B3_PolynomialRank
import PV_B3_BoundedLoop
namespace PV_B3_PolynomialFinite
open Aeneas Aeneas.Std Result ControlFlow PV_B3_Copy_117 PV_B3_PolynomialCounter
set_option autoImplicit false
 def body (poly : Array Q 28#usize) (powers : Array Q 3#usize)
    (p : host_arithmetic.PreparedQm31Multiplier) (s : State) : Result (ControlFlow State Q) :=
    host_arithmetic.evaluate_state_only_polynomial_loop.body poly powers p s.1 s.2
 theorem decreases (poly : Array Q 28#usize) (powers : Array Q 3#usize)
    (p : host_arithmetic.PreparedQm31Multiplier) (s t : State)
    (h : body poly powers p s = ok (cont t)) : PV_B3_PolynomialRank.rank t < PV_B3_PolynomialRank.rank s := by
  rcases s with ⟨a,i⟩
  exact PV_B3_PolynomialRank.decreases poly powers p a i t h
 theorem loop_source (poly : Array Q 28#usize) (powers : Array Q 3#usize)
    (p : host_arithmetic.PreparedQm31Multiplier) (a : Q) (i : Usize) :
    host_arithmetic.evaluate_state_only_polynomial_loop poly powers p a i =
      PV_B3_BoundedLoop.bounded (body poly powers p) i.val (a,i) := by
  exact PV_B3_BoundedLoop.source_eq_bounded (body poly powers p) PV_B3_PolynomialRank.rank
    (decreases poly powers p) i.val (a,i) (Nat.le_refl _)
 def reference (poly : Array Q 28#usize) (x : Q) : Result Q := do
  let x2 ← aspis_core.field.QM31.square x
  let x3 ← aspis_core.field.QM31.mul x x2
  let x4 ← aspis_core.field.QM31.square x2
  let p ← host_arithmetic.PreparedQm31Multiplier.new x4
  let powers := Array.make 3#usize [x,x2,x3]
  let a ← host_arithmetic.evaluate_state_only_polynomial.block_value poly powers 6#usize
  PV_B3_BoundedLoop.bounded (body poly powers p) 6 (a,6#usize)
 theorem source_complete (poly : Array Q 28#usize) (x : Q) :
    host_arithmetic.evaluate_state_only_polynomial poly x = reference poly x := by
  unfold host_arithmetic.evaluate_state_only_polynomial reference
  simp only [loop_source]
  rfl
#print axioms body
#print axioms decreases
#print axioms loop_source
#print axioms reference
#print axioms source_complete
end PV_B3_PolynomialFinite
