import RPz7_F3U_RangePolynomial
set_option autoImplicit false
namespace AspisR1.F3U_RangeChord
open F3U_RangePolynomial

theorem chord (hi Q : Nat) (positive : 0<hi) (below : Q≤hi)
    (left : gap 0≤0) (right : gap hi≤0) : gap Q≤0 := by
  let a : Rat := 12/(2:Rat)^256
  let b : Rat := 12*(1161+2965)/(2:Rat)^256-497/(2:Rat)^109
  let z : Rat := gap 0
  have polynomial (x : Rat) : gap x=a*x^2+b*x+z := by
    dsimp [gap,a,b,z]
    ring
  have bound := BinPerQueryNumeric.quadratic_interval a b z hi Q
    (by dsimp [a];positivity) (by exact_mod_cast positive)
    (by exact_mod_cast Nat.zero_le Q) (by exact_mod_cast below)
    left
    (by simpa only [polynomial] using right)
  simpa only [polynomial] using bound

#print axioms chord
end AspisR1.F3U_RangeChord
