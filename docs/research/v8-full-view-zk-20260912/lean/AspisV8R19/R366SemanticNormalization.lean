import AspisV8R17.StructuredCube
import AspisV8R17.MaskWeightVector
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic.LinearCombination

/-! Universal fixed-prefix normalization of finite round polynomials.
This file does not establish the source interpolation degree/boundaries,
source terminal equality, legal correction coverage, or a causal simulator.
No challenge is divided by or assumed nondegenerate. -/
set_option autoImplicit false
namespace AspisR19.R366SemanticNormalization
open AspisV8R17 Polynomial
open scoped BigOperators
variable {F : Type*} [Field F] [NeZero (2 : F)]

/-- The 26 stored high coefficients are degrees 2 through 27. -/
def tail (p : F[X]) : Fin 26 → F := fun i => p.coeff (i.val+2)

theorem finite_expansion (p : F[X]) (hp : p.natDegree ≤ 27) (x : F) :
    p.eval x = p.coeff 0 + p.coeff 1*x + ∑ i : Fin 26, tail p i*x^(i.val+2) := by
  rw [eval_eq_sum_range' (show p.natDegree < 28 by omega)]
  rw [show (28:Nat)=2+26 by decide, Finset.sum_range_add]
  have hfirst : (∑ i ∈ Finset.range 2, p.coeff i*x^i)=p.coeff 0+p.coeff 1*x := by
    simp [Finset.sum_range_succ]
  rw [hfirst,Finset.sum_range]
  simp only [tail,Nat.add_comm 2]


/-- Reconstruct the omitted linear coefficient from the actual boundary sum. -/
theorem normalized_round (p : F[X]) (hp : p.natDegree ≤ 27) (carry x : F)
    (hb : p.eval 0+p.eval 1=carry) :
    p.eval x = semanticRound carry (p.coeff 0-carry/2) (tail p) x := by
  have hx := finite_expansion p hp x
  have h0 := finite_expansion p hp 0
  have h1 := finite_expansion p hp 1
  have hb' : 2*p.coeff 0+p.coeff 1+∑ i : Fin 26, tail p i=carry := by
    have hz : (∑ i : Fin 26, tail p i*(0:F)^(i.val+2))=0 := by
      apply Finset.sum_eq_zero
      intro i _
      simp
    simp only [pow_zero, zero_mul, mul_zero, one_pow, mul_one] at h0 h1
    rw [hz] at h0
    rw [h0,h1] at hb
    linear_combination hb
  have hs : (∑ i : Fin 26, tail p i*(x^(i.val+2)-x)) =
      (∑ i : Fin 26, tail p i*x^(i.val+2))-(∑ i : Fin 26, tail p i)*x := by
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
  rw [hx]
  simp only [semanticRound, roundEval, hs]
  field_simp
  linear_combination 2*x*hb'

/-- A walk's boundaries and degree are checked at its original incoming carry. -/
def validWalk : (r : Nat) → F → RoundCoins F[X] r → RoundCoins F r → Prop
  | 0, _, _, _ => True
  | r+1, carry, ps, z => ps.1.natDegree ≤ 27 ∧ ps.1.eval 0+ps.1.eval 1=carry ∧
      validWalk r (ps.1.eval z.1) ps.2 z.2

def walk : (r : Nat) → F → RoundCoins F[X] r → RoundCoins F r → F
  | 0, carry, _, _ => carry
  | r+1, _, ps, z => walk r (ps.1.eval z.1) ps.2 z.2

def coordinates : (r : Nat) → F → RoundCoins F[X] r → RoundCoins F r →
    RoundCoins (F × (Fin 26 → F)) r
  | 0, _, _, _ => PUnit.unit
  | r+1, carry, ps, z =>
      ((ps.1.coeff 0-carry/2, tail ps.1),coordinates r (ps.1.eval z.1) ps.2 z.2)

theorem normalized_walk (r : Nat) (carry : F) (ps : RoundCoins F[X] r)
    (z : RoundCoins F r) (h : validWalk r carry ps z) :
    structuredMask r carry (coordinates r carry ps z) z=walk r carry ps z := by
  induction r generalizing carry with
  | zero => rfl
  | succ r ih =>
    rcases h with ⟨hd,hb,ht⟩
    simp only [coordinates,structuredMask,walk]
    rw [← normalized_round ps.1 hd carry z.1 hb]
    exact ih (ps.1.eval z.1) ps.2 z.2 ht

def subtractCoins : (r : Nat) → RoundCoins (F × (Fin 26 → F)) r →
    RoundCoins (F × (Fin 26 → F)) r → RoundCoins (F × (Fin 26 → F)) r
  | 0, _, _ => PUnit.unit
  | r+1, a, b => ((a.1.1-b.1.1,fun i => a.1.2 i-b.1.2 i),subtractCoins r a.2 b.2)

theorem structured_sub (r : Nat) (a b : F)
    (ca cb : RoundCoins (F × (Fin 26 → F)) r) (z : RoundCoins F r) :
    structuredMask r (a-b) (subtractCoins r ca cb) z=
      structuredMask r a ca z-structuredMask r b cb z := by
  induction r generalizing a b with
  | zero => rfl
  | succ r ih =>
    simp only [structuredMask,subtractCoins]
    have he : semanticRound (a-b) (ca.1.1-cb.1.1) (fun i => ca.1.2 i-cb.1.2 i) z.1=
        semanticRound a ca.1.1 ca.1.2 z.1-semanticRound b cb.1.1 cb.1.2 z.1 := by
      simp only [semanticRound,roundEval,sub_mul,Finset.sum_sub_distrib,sub_div]
      ring
    rw [he]
    exact ih _ _ ca.2 cb.2 z.2

/-- Universal semantic compatibility reduction, including the initial coordinate.
Its endpoint premise must be proved from the actual retained source terminal. -/
theorem terminal_compatibility (r : Nat) (a b : F)
    (pa pb : RoundCoins F[X] r) (z : RoundCoins F r)
    (ha : validWalk r a pa z) (hb : validWalk r b pb z)
    (ht : walk r a pa z=walk r b pb z) :
    structuredMask r (a-b)
      (subtractCoins r (coordinates r a pa z) (coordinates r b pb z)) z=0 := by
  rw [structured_sub,normalized_walk r a pa z ha,normalized_walk r b pb z hb,ht,sub_self]

/-- The complete 271-coordinate covector uses the same initial carry difference. -/
theorem full_271_compatibility (a b : F) (pa pb : RoundCoins F[X] 10)
    (z : RoundCoins F 10) (ha : validWalk 10 a pa z) (hb : validWalk 10 b pb z)
    (ht : walk 10 a pa z=walk 10 b pb z) :
    (∑ i : Fin 271, maskWeights271 (1/2:F) z i *
      maskCoins271 (a-b) (subtractCoins 10 (coordinates 10 a pa z) (coordinates 10 b pb z)) i)=0 := by
  rw [maskWeights271_structuredMask]
  exact terminal_compatibility 10 a b pa pb z ha hb ht

#print axioms finite_expansion
#print axioms normalized_round
#print axioms normalized_walk
#print axioms structured_sub
#print axioms terminal_compatibility
#print axioms full_271_compatibility
end AspisR19.R366SemanticNormalization
