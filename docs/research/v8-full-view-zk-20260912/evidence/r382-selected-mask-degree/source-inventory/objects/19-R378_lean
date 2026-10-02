import AspisV8R19.R376SimplePointDegree

/-! Polynomial degree accounting for two fifth-power rounds and constant
linear layers. The matrix/constants are declared exact-field data; matching
every selected Rust arithmetic/packing operation remains a source obligation. -/
set_option autoImplicit false
namespace AspisR19.R378PairedFifthDegree
open Polynomial R374SingleCoordinateDegree R376SimplePointDegree
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F]

def linearLayer {m n : Nat} (matrix : Fin m → Fin n → F)
    (state : Fin n → F[X]) : Fin m → F[X] :=
  fun k => ∑ i : Fin n, C (matrix k i)*state i

theorem linear_degree {m n d : Nat} (matrix : Fin m → Fin n → F)
    (state : Fin n → F[X]) (hs : ∀ i, (state i).natDegree ≤ d) (k : Fin m) :
    (linearLayer matrix state k).natDegree ≤ d := by
  apply natDegree_sum_le_of_forall_le
  intro i _
  apply natDegree_mul_le.trans
  simpa only [natDegree_C,zero_add] using hs i

def fifthRound {m n : Nat} (matrix : Fin m → Fin n → F)
    (constants state : Fin n → F[X]) : Fin m → F[X] :=
  linearLayer matrix (fun i => (state i+constants i)^5)

theorem fifth_degree {m n d : Nat} (matrix : Fin m → Fin n → F)
    (constants state : Fin n → F[X])
    (hc : ∀ i, (constants i).natDegree ≤ d)
    (hs : ∀ i, (state i).natDegree ≤ d) (k : Fin m) :
    (fifthRound matrix constants state k).natDegree ≤ 5*d := by
  apply linear_degree
  intro i
  exact natDegree_pow_le_of_le 5 (natDegree_add_le_of_degree_le (hs i) (hc i))

theorem paired_fifth_degree {n : Nat} (m0 m1 : Fin n → Fin n → F)
    (c0 c1 state : Fin n → F[X])
    (hc0 : ∀ i, (c0 i).natDegree ≤ 1)
    (hc1 : ∀ i, (c1 i).natDegree ≤ 1)
    (hs : ∀ i, (state i).natDegree ≤ 1) (k : Fin n) :
    (fifthRound m1 c1 (fifthRound m0 c0 state) k).natDegree ≤ 25 := by
  apply fifth_degree (d := 5)
  · intro i
    exact (hc1 i).trans (by decide)
  · exact fifth_degree m0 c0 state hc0 hs

def absorbedState {n : Nat} (tables : Fin n → Fin 1024 → F)
    (absorb : Fin n → Bool) (z : Fin 10 → F) (j : Fin 10) : Fin n → F[X] :=
  fun i => claimPolynomial (tables i) z j 0+
    if absorb i then claimPolynomial (tables i) z j 2 else 0

theorem absorbed_degree {n : Nat} (tables : Fin n → Fin 1024 → F)
    (absorb : Fin n → Bool) (z : Fin 10 → F) (j : Fin 10) (i : Fin n) :
    (absorbedState tables absorb z j i).natDegree ≤ 1 := by
  apply natDegree_add_le_of_degree_le
  · exact simple_claim_degree (tables i) z j 0 (by decide)
  · by_cases h : absorb i
    · simp only [if_pos h]
      exact simple_claim_degree (tables i) z j 2 (by decide)
    · simp only [if_neg h,natDegree_zero]
      omega

theorem leading_pair_degree {n : Nat} (tables : Fin n → Fin 1024 → F)
    (absorb : Fin n → Bool) (z : Fin 10 → F) (j : Fin 10)
    (external m0 m1 : Fin n → Fin n → F) (c0 c1 : Fin n → F) (k : Fin n) :
    (fifthRound m1 (fun i => C (c1 i))
      (fifthRound m0 (fun i => C (c0 i))
        (linearLayer external (absorbedState tables absorb z j))) k).natDegree ≤ 25 := by
  apply paired_fifth_degree
  · intro i; simp
  · intro i; simp
  · exact linear_degree external _ (absorbed_degree tables absorb z j)

#print axioms linear_degree
#print axioms fifth_degree
#print axioms paired_fifth_degree
#print axioms absorbed_degree
#print axioms leading_pair_degree
end
end AspisR19.R378PairedFifthDegree
