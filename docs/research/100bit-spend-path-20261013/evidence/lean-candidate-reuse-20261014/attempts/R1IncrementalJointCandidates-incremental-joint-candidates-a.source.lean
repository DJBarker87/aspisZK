import R1PartialJointList

/-! One selected-coordinate product/update/filter step for finite candidate
families. This is explicit finite-list plumbing, not a decoder algorithm. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.IncrementalJointCandidates

open AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.InitialEncoder
open AspisR1.PartialJointList

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

def advance (S : Finset (Fin 29)) (lane : Fin 29)
    (W : Fin 29 → InitialWord K)
    (family : Finset (Fin 29 → InitialMessage K))
    (decoded : Finset (InitialMessage K)) : Finset (Fin 29 → InitialMessage K) :=
  ((family.product decoded).image
    (fun pair => Function.update pair.1 lane pair.2)).filter
      (fun t => 38230 ≤ (selectedSupport (insert lane S) W t).card)

theorem advance_supported (S : Finset (Fin 29)) (lane : Fin 29)
    (W : Fin 29 → InitialWord K)
    (family : Finset (Fin 29 → InitialMessage K))
    (decoded : Finset (InitialMessage K))
    (hzero : ∀ t ∈ family, ∀ l, l ∉ S → t l = 0) :
    ∀ t ∈ advance S lane W family decoded, ∀ l, l ∉ insert lane S → t l = 0 := by
  classical
  intro t ht l hl
  rcases Finset.mem_filter.mp ht with ⟨_, hmem⟩
  rcases Finset.mem_image.mp hmem with ⟨pair, hp, rfl⟩
  rcases Finset.mem_product.mp hp with ⟨hfamily, _⟩
  have hlane : l ≠ lane := by
    intro heq
    subst l
    exact hl (Finset.mem_insert_self lane S)
  have hS : l ∉ S := fun h => hl (Finset.mem_insert_of_mem h)
  simpa [Function.update_of_ne hlane] using hzero pair.1 hfamily l hS

theorem advance_card_le_100 (S : Finset (Fin 29)) (lane : Fin 29)
    (W : Fin 29 → InitialWord K)
    (family : Finset (Fin 29 → InitialMessage K))
    (decoded : Finset (InitialMessage K))
    (hzero : ∀ t ∈ family, ∀ l, l ∉ S → t l = 0)
    (hclose : ∀ t ∈ advance S lane W family decoded,
      38230 ≤ (selectedSupport (insert lane S) W t).card) :
    (advance S lane W family decoded).card ≤ 100 := by
  exact PartialJointList.partial_family_card_le_100 (insert lane S) W
    (advance S lane W family decoded)
    (advance_supported S lane W family decoded hzero) hclose

theorem unfiltered_image_card_le (S : Finset (Fin 29)) (lane : Fin 29)
    (family : Finset (Fin 29 → InitialMessage K))
    (decoded : Finset (InitialMessage K)) :
    ((family.product decoded).image
      (fun pair => Function.update pair.1 lane pair.2)).card ≤
        family.card * decoded.card := by
  calc
    _ ≤ (family.product decoded).card := Finset.card_image_le
    _ = family.card * decoded.card := Finset.card_product

theorem unfiltered_image_card_le_10000 (S : Finset (Fin 29)) (lane : Fin 29)
    (family : Finset (Fin 29 → InitialMessage K))
    (decoded : Finset (InitialMessage K))
    (hfamily : family.card ≤ 100) (hdecoded : decoded.card ≤ 100) :
    ((family.product decoded).image
      (fun pair => Function.update pair.1 lane pair.2)).card ≤ 10000 := by
  calc
    _ ≤ family.card * decoded.card := unfiltered_image_card_le S lane family decoded
    _ ≤ 100 * 100 := Nat.mul_le_mul hfamily hdecoded
    _ = 10000 := by norm_num

theorem projectMessage_insert (S : Finset (Fin 29)) (lane : Fin 29)
    (t : Fin 29 → InitialMessage K) :
    projectMessage (insert lane S) t =
      Function.update (projectMessage S t) lane (t lane) := by
  funext j
  by_cases hj : j = lane
  · subst j
    simp [projectMessage]
  · simp [projectMessage, hj]

#print axioms advance_supported
#print axioms advance_card_le_100
#print axioms unfiltered_image_card_le
#print axioms unfiltered_image_card_le_10000
#print axioms projectMessage_insert

end AspisR1.IncrementalJointCandidates
end
