import AspisV8R19.R378PairedFifthDegree

set_option autoImplicit false
namespace AspisR19.R380InternalFifthDegree
open Polynomial AspisR19.R378PairedFifthDegree
noncomputable section
variable {F : Type*} [Field F]

def internalRound {n : Nat} (matrix : Fin n → Fin n → F)
    (active : Fin n → Bool) (constants state : Fin n → F[X]) : Fin n → F[X] :=
  linearLayer matrix (fun i => if active i then (state i + constants i)^5 else state i)

theorem internalRound_degree {n d : Nat} (matrix : Fin n → Fin n → F)
    (active : Fin n → Bool) (constants state : Fin n → F[X])
    (hc : ∀ i, (constants i).natDegree ≤ d)
    (hs : ∀ i, (state i).natDegree ≤ d) (k : Fin n) :
    (internalRound matrix active constants state k).natDegree ≤ 5*d := by
  apply linear_degree
  intro i
  by_cases h : active i
  · rw [if_pos h]
    exact natDegree_pow_le_of_le 5 (natDegree_add_le_of_degree_le (hs i) (hc i))
  · rw [if_neg h]
    exact (hs i).trans (by omega)

theorem two_internalRounds_degree {n : Nat}
    (m0 m1 : Fin n → Fin n → F) (a0 a1 : Fin n → Bool)
    (c0 c1 state : Fin n → F[X])
    (hc0 : ∀ i, (c0 i).natDegree ≤ 1)
    (hc1 : ∀ i, (c1 i).natDegree ≤ 1)
    (hs : ∀ i, (state i).natDegree ≤ 1) (k : Fin n) :
    (internalRound m1 a1 c1 (internalRound m0 a0 c0 state) k).natDegree ≤ 25 := by
  apply internalRound_degree (d := 5)
  · intro i
    exact (hc1 i).trans (by decide)
  · exact internalRound_degree m0 a0 c0 state hc0 hs

#print axioms internalRound_degree
#print axioms two_internalRounds_degree
end
end AspisR19.R380InternalFifthDegree
