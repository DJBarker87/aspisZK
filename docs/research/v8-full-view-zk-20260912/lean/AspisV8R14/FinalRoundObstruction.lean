import Mathlib.Tactic.Ring
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.VecNotation

/-!
Five high coefficients of a linear polynomial times a shifted 26th power.
All other allowed fixed-C1 mask/H1 responses have degree <=22. The three
functionals below vanish on G for EVERY shift, not merely sampled prefixes.
DRAFT: not compiled in the packet-building environment.
-/
set_option autoImplicit false
namespace AspisV8R14
variable {K : Type*} [CommRing K]

/-- Coordinates correspond to c23,c24,c25,c26,c27. The common nonzero c^26
scaling has been absorbed into b0 and b1. -/
def gHigh (a b0 b1 : K) : Fin 5 → K := ![
  2600*a^3*b0 + 14950*a^4*b1,
  325*a^2*b0 + 2600*a^3*b1,
  26*a*b0 + 325*a^2*b1,
  b0 + 26*a*b1,
  b1]

def obstruction23 (a : K) (v : Fin 5 → K) : K :=
  v 0 - 2600*a^3*v 3 + 52650*a^4*v 4

def obstruction24 (a : K) (v : Fin 5 → K) : K :=
  v 1 - 325*a^2*v 3 + 5850*a^3*v 4

def obstruction25 (a : K) (v : Fin 5 → K) : K :=
  v 2 - 26*a*v 3 + 351*a^2*v 4

theorem three_high_invariants (a b0 b1 : K) :
    obstruction23 a (gHigh a b0 b1) = 0 ∧
    obstruction24 a (gHigh a b0 b1) = 0 ∧
    obstruction25 a (gHigh a b0 b1) = 0 := by
  constructor
  · simp [obstruction23, gHigh]; ring
  constructor
  · simp [obstruction24, gHigh]; ring
  · simp [obstruction25, gHigh]; ring

theorem low_degree_response_does_not_change_high_invariants
    (a : K) (v delta : Fin 5 → K) (zero : ∀ i, delta i = 0) :
    obstruction23 a (v + delta) = obstruction23 a v ∧
    obstruction24 a (v + delta) = obstruction24 a v ∧
    obstruction25 a (v + delta) = obstruction25 a v := by
  simp [obstruction23, obstruction24, obstruction25, zero]

theorem independent_obstructions (a x y z : K) :
    obstruction23 a (![x,y,z,0,0] : Fin 5 → K) = x ∧
    obstruction24 a (![x,y,z,0,0] : Fin 5 → K) = y ∧
    obstruction25 a (![x,y,z,0,0] : Fin 5 → K) = z := by
  simp [obstruction23, obstruction24, obstruction25]

#print axioms three_high_invariants
#print axioms independent_obstructions
end AspisV8R14
