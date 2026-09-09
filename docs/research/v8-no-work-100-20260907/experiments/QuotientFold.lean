import Mathlib.Tactic
namespace AspisV8.QuotientFold
variable {R : Type*} [CommRing R]
def sequential (h a ix iy v0 v1 v2 v3 : R) :=
  let pos := (v0+v1)*h+a*((v0-v1)*iy)
  let neg := (v2+v3)*h-a*((v2-v3)*iy)
  (pos+neg)*h+a^2*((pos-neg)*ix)
def expanded (h a ix iy v0 v1 v2 v3 : R) :=
  (v0+v1+(v2+v3))*h*h+
    (a*((v0-v1-(v2-v3))*(iy*h))+
     a^2*((v0+v1-(v2+v3))*(ix*h))+
     a^3*((v0-v1+(v2-v3))*(ix*iy)))
-- No honest-proof, nonzero-coordinate or actual-inverse premise is needed.
theorem fold_identity (h a ix iy v0 v1 v2 v3 : R) :
    expanded h a ix iy v0 v1 v2 v3=sequential h a ix iy v0 v1 v2 v3 := by
  dsimp [expanded,sequential]
  ring
theorem prepared_powers (a : R) : (a^2)*a=a^3 := by ring
theorem zero_challenge (h ix iy v0 v1 v2 v3 : R) :
    expanded h 0 ix iy v0 v1 v2 v3=(v0+v1+(v2+v3))*h*h := by
  simp [expanded]
-- Moving the minus-y pair into the wrong slot is observably not equivalent.
theorem slot_sign_counterexample :
    sequential (1:ℤ) 2 3 5 0 0 1 0 ≠ sequential (1:ℤ) 2 3 5 0 0 0 1 := by
  norm_num [sequential]
#print axioms fold_identity
#print axioms prepared_powers
#print axioms zero_challenge
#print axioms slot_sign_counterexample
end AspisV8.QuotientFold
