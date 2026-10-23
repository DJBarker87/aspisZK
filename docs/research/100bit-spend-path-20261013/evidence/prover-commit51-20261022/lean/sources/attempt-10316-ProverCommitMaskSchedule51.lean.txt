import R1Z.ProverCommitMaskPolynomial50
/-! One injective schedule for the two source write loops. -/
set_option autoImplicit false
namespace R1Z.ProverCommitMaskSchedule51
open scoped BigOperators

def exponent (i : Nat) : Nat :=
  if i<14 then 2*i else if i=14 then 13 else if i=15 then 25
  else if i<22 then 2*(i-16)+1 else 2*(i-16)+3

theorem bound (i : Fin 26) : exponent i.val<27 := by
  have := i.isLt
  dsimp only [exponent]
  split_ifs <;> omega

theorem injective : Function.Injective (fun i : Fin 26 => exponent i.val) := by
  intro i j hij
  apply Fin.ext
  have := i.isLt
  have := j.isLt
  dsimp only [exponent] at hij
  split_ifs at hij <;> omega

theorem first (i : Fin 16) : exponent i.val=(R0P.Mask.factorExponent i).val := by
  have := i.isLt
  dsimp only [exponent,R0P.Mask.factorExponent]
  split_ifs <;> omega

theorem second (i : Fin 10) : exponent (16+i.val)=(R0P.Mask.maskOnlyFactorExponent i).val := by
  have := i.isLt
  dsimp only [exponent,R0P.Mask.maskOnlyFactorExponent]
  split_ifs <;> omega

theorem omitted (i : Fin 26) : exponent i.val≠23 := by
  have := i.isLt
  dsimp only [exponent]
  split_ifs <;> omega

#print axioms bound
#print axioms injective
#print axioms first
#print axioms second
#print axioms omitted
end R1Z.ProverCommitMaskSchedule51
