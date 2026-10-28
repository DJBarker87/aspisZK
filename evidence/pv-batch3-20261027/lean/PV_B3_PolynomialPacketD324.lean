import PV_B3_PolynomialEmission
import PV_B3_Result
import PV_B3_PrefixRank222
import PV_B3_BoundedLoop
namespace PV_B3_PolynomialPacketD324
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

 def rank (s : State) : Nat := s.2.val
 theorem rank_step (poly : Array Q 28#usize) (powers : Array Q 3#usize)
    (p : host_arithmetic.PreparedQm31Multiplier) (a : Q) (i : Usize) (next : State)
    (h : host_arithmetic.evaluate_state_only_polynomial_loop.body poly powers p a i = ok (cont next)) :
    rank next < rank (a,i) := by
  have hc := body_counter poly powers p a i (cont next) h
  change next.2 = Usize.wrapping_sub i 1#usize at hc
  have hi : 0 < i.val := by
    unfold host_arithmetic.evaluate_state_only_polynomial_loop.body at h
    split at h
    · assumption
    · cases h
  unfold rank
  dsimp only
  rw [hc,PV_B3_PrefixRank222.decrement i hi]
  omega

 def body (poly : Array Q 28#usize) (powers : Array Q 3#usize)
    (p : host_arithmetic.PreparedQm31Multiplier) (s : State) : Result (ControlFlow State Q) :=
    host_arithmetic.evaluate_state_only_polynomial_loop.body poly powers p s.1 s.2
 theorem decreases (poly : Array Q 28#usize) (powers : Array Q 3#usize)
    (p : host_arithmetic.PreparedQm31Multiplier) (s t : State)
    (h : body poly powers p s = ok (cont t)) : rank t < rank s := by
  rcases s with ⟨a,i⟩
  exact rank_step poly powers p a i t h
 theorem loop_source (poly : Array Q 28#usize) (powers : Array Q 3#usize)
    (p : host_arithmetic.PreparedQm31Multiplier) (a : Q) (i : Usize) :
    host_arithmetic.evaluate_state_only_polynomial_loop poly powers p a i =
      PV_B3_BoundedLoop.bounded (body poly powers p) i.val (a,i) := by
  exact PV_B3_BoundedLoop.source_eq_bounded (body poly powers p) rank
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

#print axioms Progress
#print axioms body_counter
#print axioms rank
#print axioms rank_step
#print axioms body
#print axioms decreases
#print axioms loop_source
#print axioms reference
#print axioms source_complete
end PV_B3_PolynomialPacketD324
