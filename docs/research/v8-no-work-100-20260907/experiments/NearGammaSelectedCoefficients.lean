import NearGammaSelectedC1
import PartialFoldRecovery

/-! Coefficient equality, not only equality of encoded words, for the
constructed selected gamma cover. No honest-table equality is assumed. -/
set_option autoImplicit false
set_option maxRecDepth 200
set_option maxHeartbeats 20000
namespace AspisV8.NearGammaSelectedCoefficients
open Finset
open AspisV8.NearGammaSelectedC1 AspisV8.NearGammaMessageCover
open AspisV8.EarlyC1Projection AspisV8.EarlyC1LateProjection
open AspisV8.NearGammaFibreBridge AspisV8.PartialFoldRecovery
open AspisPool.V7C1ConcreteProjectionBinding
open AspisV5ComponentCConcreteFoldLinearity
noncomputable section
noncomputable local instance : Fintype (Fin 262144) :=
  AspisV8.EarlyC1Specialization.explicit_instance

/-- Actual selected code coefficients are unique, using the proved complete
fibre overlap cap. Neither finite domain nor field enumeration is reduced. -/
theorem fibreEncode_injective : Function.Injective fibreEncode := by
  intro left right same
  by_contra different
  have cap := AspisV8.EarlyC1Identification.matching_set_cap left right different univ
    (fun f _ => congrFun same f)
  rw [domain_card] at cap
  omega

theorem reversed_slot_mismatch {Slot : Type*} (left right : Slot → K) :
    (∃ slot, left slot ≠ right slot) ↔ right ≠ left := by
  rw [Function.ne_iff]
  exact exists_congr (fun _ => ne_comm)

/-- Same actual fibre set, with the raw received-minus-encoded orientation
used by NearGamma and the encoded-minus-raw orientation used by fibreBad. -/
theorem fibreBad_raw_eq (message : Message) (received : Fin 1048576 → K) :
    fibreBad (m := 262144) (exactInitialEncoder message) received =
      (univ.filter fun f : Fin 262144 =>
        (fun s : Fin 4 => received (fibreEmbed (f,s))) ≠ fibreEncode message f) := by
  classical
  ext f
  simp only [fibreBad,mem_filter,mem_univ,true_and]
  exact reversed_slot_mismatch
    (fun s => exactInitialEncoder message (childIndex f s))
    (fun s => received (childIndex f s))

theorem near_of_fibreBad (c1 : C1Received) (c2 : C2Received) (gamma : K)
    (message : Message)
    (close : (fibreBad (m := 262144) (exactInitialEncoder message)
      (rawBatch c1 c2 gamma)).card ≤ 9301) :
    near c1 c2 gamma (fibreEncode message) := by
  apply (near_encoded_iff c1 c2 gamma message).mpr
  rw [fibreBad_raw_eq] at close
  exact close

/-- The dense branch's fixed coefficient tuple covers the literal original
message of every near candidate, including one selected after gamma. -/
theorem coefficient_cover_dichotomy (c1 : C1Received) (c2 : C2Received)
    (G : Finset K) :
    (NearGammaSelectedC1.good c1 c2 G).card<64 ∨
      ∃ p : Fin 29 → Message,
        245609 ≤ (support fibreEncode (fibreWord29 c1 c2) p).card ∧
        earlyC1 c1=some (c1Projection p) ∧
        ∀ gamma ∈ G, ∀ message : Message,
          near c1 c2 gamma (fibreEncode message) → message=batch p gamma := by
  rcases selected_gamma_c1_dichotomy c1 c2 G with sparse | ⟨p,own,early,covered⟩
  · exact Or.inl sparse
  · refine Or.inr ⟨p,own,early,?_⟩
    intro gamma hg message hm
    exact fibreEncode_injective (covered gamma hg (fibreEncode message) hm)

theorem raw_message_cover_dichotomy (c1 : C1Received) (c2 : C2Received)
    (G : Finset K) :
    (NearGammaSelectedC1.good c1 c2 G).card<64 ∨
      ∃ p : Fin 29 → Message,
        245609 ≤ (support fibreEncode (fibreWord29 c1 c2) p).card ∧
        earlyC1 c1=some (c1Projection p) ∧
        ∀ gamma ∈ G, ∀ message : Message,
          (fibreBad (m := 262144) (exactInitialEncoder message)
            (rawBatch c1 c2 gamma)).card≤9301 → message=batch p gamma := by
  rcases coefficient_cover_dichotomy c1 c2 G with sparse | ⟨p,own,early,covered⟩
  · exact Or.inl sparse
  · refine Or.inr ⟨p,own,early,?_⟩
    intro gamma hg message hm
    exact covered gamma hg message (near_of_fibreBad c1 c2 gamma message hm)

#print axioms fibreEncode_injective
#print axioms reversed_slot_mismatch
#print axioms fibreBad_raw_eq
#print axioms near_of_fibreBad
#print axioms coefficient_cover_dichotomy
#print axioms raw_message_cover_dichotomy
end
end AspisV8.NearGammaSelectedCoefficients
