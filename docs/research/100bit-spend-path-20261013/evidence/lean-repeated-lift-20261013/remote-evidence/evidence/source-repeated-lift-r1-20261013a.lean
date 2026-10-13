import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Omega

/-! Abstract repeated-fibre projection and agreement descent.

This file proves only finite-set cardinality and a conditional algebraic
projection-descent lemma. Its encoder projection identity and agreement bound
are explicit hypotheses; a concrete E256 encoder instantiation is pending.
No protocol, decoder, privacy, or security theorem is claimed. -/

set_option autoImplicit false

noncomputable section

namespace AspisR1

variable {V M N K : Type*} [Fintype V] [DecidableEq V] [Field K]

local instance : DecidableEq K := Classical.decEq K

/-- The repeated support comprises a complete four-lane fibre above each
base point in `S`. -/
def repeatedSupport (S : Finset V) : Finset (V × Fin 4) :=
  S.product (Finset.univ : Finset (Fin 4))

theorem repeated_support_card (S : Finset V) :
    (repeatedSupport S).card = 4 * S.card := by
  simp [repeatedSupport, Finset.card_product]

/-- A base support of size at least 2390 lifts to at least 9560 repeated
coordinates. -/
theorem repeated_support_card_ge_9560 (S : Finset V)
    (hS : 2390 ≤ S.card) :
    9560 ≤ (repeatedSupport S).card := by
  rw [repeated_support_card]
  omega

/-- If the original encoding is constant on each complete fibre above `S`,
and the projection encoding is the fibre mean, then the two encodings agree
on the repeated support. -/
theorem repeated_projection_agrees_on_support
    (S : Finset V) (enc : M → V × Fin 4 → K) (project : M → M)
    (a : M) (g : V → K)
    (hfour : ∀ v ∈ S, ∀ s : Fin 4, enc a (v, s) = g v)
    (hmean : ∀ v j, enc (project a) (v, j) =
      (∑ s : Fin 4, enc a (v, s)) / 4)
    (h4 : (4 : K) ≠ 0) :
    ∀ p ∈ repeatedSupport S, enc a p = enc (project a) p := by
  classical
  rintro ⟨v, j⟩ hp
  simp only [repeatedSupport, Finset.mem_product, Finset.mem_univ, true_and] at hp
  have hconstant : ∀ s : Fin 4, enc a (v, s) = g v := hfour v hp
  have hsum : (∑ s : Fin 4, enc a (v, s)) = (4 : K) * g v := by
    simp_rw [hconstant]
    simp
  calc
    enc a (v, j) = g v := hconstant j
    _ = ((4 : K) * g v) / 4 := by field_simp [h4]
    _ = enc (project a) (v, j) := by rw [← hsum, hmean]

/-- Complete four-lane agreement forces an element to equal its projection,
provided distinct messages have at most 255 agreement coordinates. -/
theorem repeated_lift_projection_descent
    (S : Finset V) (enc : M → V × Fin 4 → K) (project : M → M)
    (a : M) (g : V → K)
    (hfour : ∀ v ∈ S, ∀ s : Fin 4, enc a (v, s) = g v)
    (hmean : ∀ v j, enc (project a) (v, j) =
      (∑ s : Fin 4, enc a (v, s)) / 4)
    (h4 : (4 : K) ≠ 0)
    (hS : 64 ≤ S.card)
    (hoverlap : ∀ b c, b ≠ c →
      (Finset.univ.filter (fun p : V × Fin 4 => enc b p = enc c p)).card ≤ 255) :
    a = project a := by
  classical
  let agree : Finset (V × Fin 4) :=
    Finset.univ.filter (fun p => enc a p = enc (project a) p)
  have hsubset : repeatedSupport S ⊆ agree := by
    intro p hp
    simp only [agree, Finset.mem_filter, Finset.mem_univ, true_and]
    exact repeated_projection_agrees_on_support S enc project a g hfour hmean h4 p hp
  have hsupport : 256 ≤ (repeatedSupport S).card := by
    rw [repeated_support_card]
    omega
  have hagree : 256 ≤ agree.card := by
    exact hsupport.trans (Finset.card_le_card hsubset)
  by_contra hne
  have hneq : a ≠ project a := by simpa using hne
  have hupper := hoverlap a (project a) hneq
  simp only [agree] at hagree
  omega

/-- If the projection is known to factor through a lift and a decoder, the
same conditional descent yields the corresponding lift-decoder identity. -/
theorem repeated_lift_descent_via_lift
    (S : Finset V) (enc : M → V × Fin 4 → K) (project : M → M)
    (a : M) (g : V → K)
    (hfour : ∀ v ∈ S, ∀ s : Fin 4, enc a (v, s) = g v)
    (hmean : ∀ v j, enc (project a) (v, j) =
      (∑ s : Fin 4, enc a (v, s)) / 4)
    (h4 : (4 : K) ≠ 0)
    (hS : 64 ≤ S.card)
    (hoverlap : ∀ b c, b ≠ c →
      (Finset.univ.filter (fun p : V × Fin 4 => enc b p = enc c p)).card ≤ 255)
    (L : N → M) (D : M → N) (hfactor : project a = L (D a)) :
    a = L (D a) := by
  rw [← hfactor]
  exact repeated_lift_projection_descent S enc project a g hfour hmean h4 hS hoverlap

#print axioms repeated_support_card
#print axioms repeated_support_card_ge_9560
#print axioms repeated_projection_agrees_on_support
#print axioms repeated_lift_projection_descent
#print axioms repeated_lift_descent_via_lift

end AspisR1

end
