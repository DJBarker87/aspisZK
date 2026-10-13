import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fintype.Card

/-! A finite-subfield root-counting lemma for the selected batching route.

This file is purely algebraic. It makes no probability or protocol-security
claim. -/

set_option autoImplicit false

noncomputable section

namespace AspisR1

open Polynomial

variable {K E : Type*} [Field K] [Field E] [Fintype K]

local instance : DecidableEq K := Classical.decEq K
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

/-- A nonzero polynomial over `E` has at most its degree many roots among the
images in `E` of elements of the finite field `K`. -/
theorem subfield_bad_card_le_natDegree
    (iota : K →+* E) (p : E[X]) (hp : p ≠ 0) :
    (Finset.univ.filter (fun t : K => p.eval (iota t) = 0)).card ≤ p.natDegree := by
  classical
  let bad := Finset.univ.filter (fun t : K => p.eval (iota t) = 0)
  let embedding : K ↪ E := ⟨iota, iota.injective⟩
  have hsubset : bad.map embedding ⊆ p.roots.toFinset := by
    intro y hy
    rcases Finset.mem_map.mp hy with ⟨t, ht, hty⟩
    subst y
    change iota t ∈ p.roots.toFinset
    rw [Multiset.mem_toFinset, p.mem_roots hp]
    exact (Finset.mem_filter.mp ht).2
  calc
    bad.card = (bad.map embedding).card := by simp
    _ ≤ p.roots.toFinset.card := Finset.card_le_card hsubset
    _ ≤ p.roots.card := Multiset.toFinset_card_le p.roots
    _ ≤ p.natDegree := p.card_roots'

#print axioms subfield_bad_card_le_natDegree

/-- A stated natural-number degree bound gives the same bound on bad
subfield elements. -/
theorem subfield_bad_card_le_degree
    (iota : K →+* E) (p : E[X]) (hp : p ≠ 0)
    (degreeBound : Nat) (hdegree : p.natDegree ≤ degreeBound) :
    (Finset.univ.filter (fun t : K => p.eval (iota t) = 0)).card ≤ degreeBound := by
  exact (subfield_bad_card_le_natDegree iota p hp).trans hdegree

#print axioms subfield_bad_card_le_degree

/-- Degree-21 specialization of the finite-subfield root count. -/
theorem subfield_bad_card_le_21
    (iota : K →+* E) (p : E[X]) (hp : p ≠ 0)
    (hdegree : p.natDegree ≤ 21) :
    (Finset.univ.filter (fun t : K => p.eval (iota t) = 0)).card ≤ 21 := by
  exact subfield_bad_card_le_degree iota p hp 21 hdegree

#print axioms subfield_bad_card_le_21

end AspisR1

end
