import Mathlib.Tactic.Ring
set_option autoImplicit false
namespace R1Z.PV_Canon
/-- The symbolic block law needed by the remaining radix-four/Horner source
proof. No concrete field recurrence or huge numeral is reduced. -/
theorem radix_four_block {K : Type} [CommRing K] (x a b c d : K) :
    a + x*b + x^2*c + x^3*d = a + x*(b+x*(c+x*d)) := by ring
 theorem radix_four_two_blocks {K : Type} [CommRing K] (x a b c d e f g h : K) :
    (a + x*b + x^2*c + x^3*d) + x^4*(e+x*f+x^2*g+x^3*h) =
      a+x*(b+x*(c+x*(d+x*(e+x*(f+x*(g+x*h)))))) := by ring
#print axioms radix_four_block
#print axioms radix_four_two_blocks
end R1Z.PV_Canon
