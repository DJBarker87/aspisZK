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
  rcases Finset.mem_filter.mp ht with ⟨hmem, _⟩
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
    (hzero : ∀ t ∈ family, ∀ l, l ∉ S → t l = 0) :
    (advance S lane W family decoded).card ≤ 100 := by
  apply PartialJointList.partial_family_card_le_100 (insert lane S) W
    (advance S lane W family decoded)
    (advance_supported S lane W family decoded hzero)
  intro t ht
  exact (Finset.mem_filter.mp ht).2

theorem unfiltered_image_card_le (lane : Fin 29)
    (family : Finset (Fin 29 → InitialMessage K))
    (decoded : Finset (InitialMessage K)) :
    ((family.product decoded).image
      (fun pair => Function.update pair.1 lane pair.2)).card ≤
        family.card * decoded.card := by
  calc
    _ ≤ (family.product decoded).card := Finset.card_image_le
    _ = family.card * decoded.card := by
      simpa [Finset.product] using (Finset.card_product family decoded)

theorem unfiltered_image_card_le_10000 (lane : Fin 29)
    (family : Finset (Fin 29 → InitialMessage K))
    (decoded : Finset (InitialMessage K))
    (hfamily : family.card ≤ 100) (hdecoded : decoded.card ≤ 100) :
    ((family.product decoded).image
      (fun pair => Function.update pair.1 lane pair.2)).card ≤ 10000 := by
  calc
    _ ≤ family.card * decoded.card := unfiltered_image_card_le lane family decoded
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

theorem selectedSupport_project (S : Finset (Fin 29))
    (W : Fin 29 → InitialWord K) (t : Fin 29 → InitialMessage K) :
    selectedSupport S W (projectMessage S t) = selectedSupport S W t := by
  ext lane
  simp only [selectedSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h j hj
    simpa [projectMessage, hj] using h j hj
  · intro h j hj
    simpa [projectMessage, hj] using h j hj

theorem selectedSupport_projectWord (S : Finset (Fin 29))
    (W : Fin 29 → InitialWord K) (t : Fin 29 → InitialMessage K) :
    selectedSupport S (projectWord S W) t = selectedSupport S W t := by
  ext x
  simp only [selectedSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h j hj
    simpa [projectWord, hj] using h j hj
  · intro h j hj
    simpa [projectWord, hj] using h j hj

set_option maxRecDepth 8192 in
theorem projected_full_threshold (S : Finset (Fin 29))
    (W : Fin 29 → InitialWord K) (t : Fin 29 → InitialMessage K)
    (ht : t ∈ InitialResponses.Lambda W) :
    38230 ≤ (selectedSupport S W (projectMessage S t)).card := by
  have hp := PartialJointList.projected_response_mem_lambda S W t ht
  rw [InitialResponses.mem_Lambda] at hp
  rw [PartialJointList.selectedSupport_eq_joint (S := S)
    (W := projectWord S W) (t := projectMessage S t)] at hp
  rw [selectedSupport_projectWord S W (projectMessage S t)] at hp
  rw [selectedSupport_project S W t]
  exact hp

set_option maxRecDepth 8192 in
theorem advance_preserves_full_projection (S : Finset (Fin 29))
    (lane : Fin 29) (W : Fin 29 → InitialWord K)
    (family : Finset (Fin 29 → InitialMessage K))
    (decoded : Finset (InitialMessage K)) (t : Fin 29 → InitialMessage K)
    (ht : t ∈ InitialResponses.Lambda W)
    (hp : projectMessage S t ∈ family) (hd : t lane ∈ decoded) :
    projectMessage (insert lane S) t ∈ advance S lane W family decoded := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_image.mpr ⟨(projectMessage S t, t lane),
    Finset.mem_product.mpr ⟨hp, hd⟩, ?_⟩, ?_⟩
  · exact (projectMessage_insert S lane t).symm
  · exact projected_full_threshold (insert lane S) W t ht

#print axioms advance_supported
#print axioms advance_card_le_100
#print axioms unfiltered_image_card_le
#print axioms unfiltered_image_card_le_10000
#print axioms projectMessage_insert
#print axioms selectedSupport_project
#print axioms selectedSupport_projectWord
#print axioms projected_full_threshold
#print axioms advance_preserves_full_projection

end AspisR1.IncrementalJointCandidates
end
