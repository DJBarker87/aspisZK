import R1PartialJointList

/-! Concrete C1-coordinate candidate list built from the generic selected-lane
projection. This is a mathematical finite candidate list; it adds no source
parser or efficient-decoder claim. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.C1PartialCandidates

open AspisPool.AlgorithmicCircleDecoderV7

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

def c1Lanes : Finset (Fin 29) :=
  (Finset.univ.erase (26 : Fin 29)).erase (27 : Fin 29)

theorem mem_c1Lanes (lane : Fin 29) :
    lane ∈ c1Lanes ↔ lane.val < 26 ∨ lane.val = 28 := by
  simp only [c1Lanes, Finset.mem_erase, Finset.mem_univ, and_true]
  have hlt : lane.val < 29 := lane.isLt
  constructor
  · rintro ⟨h27, h26⟩
    have hv27 : lane.val ≠ 27 := by
      intro hv
      apply h27
      exact Fin.ext hv
    have hv26 : lane.val ≠ 26 := by
      intro hv
      apply h26
      exact Fin.ext hv
    omega
  · intro h
    constructor
    · intro he
      have hv := congrArg Fin.val he
      omega
    · intro he
      have hv := congrArg Fin.val he
      omega

def candidates (W : Fin 29 → InitialWord K) :
    Finset (Fin 29 → InitialMessage K) :=
  InitialResponses.Lambda (PartialJointList.projectWord c1Lanes W)

theorem candidates_card (W : Fin 29 → InitialWord K) :
    (candidates W).card ≤ 100 := by
  exact InitialResponses.Lambda_card (PartialJointList.projectWord c1Lanes W)

theorem candidates_eq_of_selected_eq
    (W W' : Fin 29 → InitialWord K)
    (hselected : ∀ lane, lane ∈ c1Lanes → W lane = W' lane) :
    candidates W = candidates W' := by
  apply congrArg InitialResponses.Lambda
  funext lane
  by_cases h : lane ∈ c1Lanes
  · simp [PartialJointList.projectWord, h, hselected lane h]
  · simp [PartialJointList.projectWord, h]

set_option maxRecDepth 8192 in
theorem projected_full_mem
    (W : Fin 29 → InitialWord K) (t : Fin 29 → InitialMessage K)
    (ht : t ∈ InitialResponses.Lambda W) :
    PartialJointList.projectMessage c1Lanes t ∈ candidates W := by
  change PartialJointList.projectMessage c1Lanes t ∈
    InitialResponses.Lambda (PartialJointList.projectWord c1Lanes W)
  exact PartialJointList.projected_response_mem_lambda c1Lanes W t ht

#print axioms mem_c1Lanes
#print axioms candidates_card
#print axioms candidates_eq_of_selected_eq
#print axioms projected_full_mem

end AspisR1.C1PartialCandidates
end
