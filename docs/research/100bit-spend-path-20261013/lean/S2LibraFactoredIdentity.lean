import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-! Source-shaped algebra for CU candidate14. Absorb the common quarter and
PERM reindexing into arbitrary A/B coefficients. This proves the 56-entry
row's four factorization identities over every commutative semiring; it does
not assert a Rust/extraction simulation or the separate inactive-mask table. -/
set_option autoImplicit false
namespace AspisR1.S2LibraFactoredIdentity
open scoped BigOperators
variable {E : Type} [CommSemiring E]

def low (A B : Fin 4 → E) (s : Fin 16) : E :=
  A ⟨s.val % 4, Nat.mod_lt _ (by decide)⟩ *
    B ⟨s.val / 4, by omega⟩

def original (A B : Fin 4 → E) (q0 q1 : E) (j : Fin 4) : E :=
  ∑ s : Fin 16,
    let index := 16*j.val+s.val
    if index < 56 then
      low A B s * (if index < 28 then q0^(index%28) else q1^(index%28))
    else 0

def scalar (A : Fin 4 → E) (q : E) : E :=
  A 0 + A 1*q + A 2*q^2 + A 3*q^3

def firstTwo (B : Fin 4 → E) (q : E) : E := B 0 + B 1*q^4

def firstThree (B : Fin 4 → E) (q : E) : E := firstTwo B q + B 2*q^8

def allFour (B : Fin 4 → E) (q : E) : E := firstThree B q + B 3*q^12

def factored (A B : Fin 4 → E) (q0 q1 : E) (j : Fin 4) : E :=
  if j.val = 0 then scalar A q0 * allFour B q0
  else if j.val = 1 then
    scalar A q0 * firstThree B q0 * q0^16 + scalar A q1 * B 3
  else if j.val = 2 then scalar A q1 * allFour B q1 * q1^4
  else scalar A q1 * firstTwo B q1 * q1^20

private theorem fin_two (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl
private theorem fin_three (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl

/-- All four old 16-position blocks equal the actual two-run factorization;
block 1 cuts after twelve coefficients, block 3 after eight. Zero and arbitrary
challenges are covered without inversion or a nonzero premise. -/
theorem original_eq_factored (A B : Fin 4 → E) (q0 q1 : E) (j : Fin 4) :
    original A B q0 q1 j = factored A B q0 q1 j := by
  fin_cases j <;>
    norm_num [original, low, factored, scalar, firstTwo, firstThree,
      allFour, Fin.sum_univ_succ] <;> simp only [fin_two, fin_three] <;> ring


def perm (r : Fin 4) : Fin 4 :=
  if r.val = 0 then 0 else if r.val = 1 then 3 else if r.val = 2 then 2 else 1

def scaled (p : Fin 4 → E) (quarter : E) (r : Fin 4) : E := p (perm r) * quarter

/-- The source low tensor's two common quarter factors are precisely the
coefficient scaling used above. This requires no invertibility of quarter. -/
theorem low_scaled (p0 p1 : Fin 4 → E) (quarter : E) (s : Fin 16) :
    low (scaled p0 quarter) (scaled p1 quarter) s =
      p0 (perm ⟨s.val % 4, Nat.mod_lt _ (by decide)⟩) *
      p1 (perm ⟨s.val / 4, by omega⟩) * (quarter * quarter) := by
  unfold low scaled
  ring

/-- Source scalar_factor moves its final quarter into every coefficient. -/
theorem scalar_scaled (p : Fin 4 → E) (quarter q : E) :
    scalar (scaled p quarter) q =
      (p (perm 0) + p (perm 1)*q + p (perm 2)*q^2 + p (perm 3)*q^3) * quarter := by
  unfold scalar scaled
  ring

/-- Candidate14's coefficient permutation and quarter scaling instantiate the
identity, including both challenge values zero and every low tensor value. -/
theorem source_scaled_eq (p0 p1 : Fin 4 → E) (quarter q0 q1 : E) (j : Fin 4) :
    original (scaled p0 quarter) (scaled p1 quarter) q0 q1 j =
      factored (scaled p0 quarter) (scaled p1 quarter) q0 q1 j :=
  original_eq_factored _ _ _ _ _

#print axioms low_scaled
#print axioms scalar_scaled
#print axioms source_scaled_eq

#print axioms original_eq_factored
end AspisR1.S2LibraFactoredIdentity
