import EarlyC1Projection

/-!
The arbitrary-set source interface has passed its focused preflight.
The concrete optional-object application below is the next changed check;
see early-c1-identification-notes.md for the precise evidence boundary.

Concrete application of the already proved optional-recovery theorem.
The source interface accepts an arbitrary supplied matching set, so no
application has to identify two independently constructed concrete filters.
The encoder, domain and actual optional object are unchanged.
-/
set_option autoImplicit false

namespace AspisV8.EarlyC1Identification
open Finset
open AspisV8.EarlyC1Projection AspisV8.NearGammaFibreBridge
open AspisPool.V7C1ConcreteProjectionBinding AspisPool.V7C1SubfieldRecovery
open AspisPool.V7ExtractedLaneWords AspisV5ComponentCQM31TowerExact

#eval IO.eprintln "EARLY_C1_IMPORT_COMPLETE"

/- A generic adapter from arbitrary witnessed support sets to the existing
generic agreement definition. The source callback never sees that filter. -/
theorem agreement_cap_from_sets {I V M : Type*} [Fintype I]
    (encode : M → I → V) (cap : ℕ)
    (source : ∀ left right, left ≠ right → ∀ good : Finset I,
      (∀ i ∈ good, encode left i = encode right i) → good.card ≤ cap) :
    ∀ left right, left ≠ right → (agreement encode left right).card ≤ cap := by
  classical
  intro left right different
  apply source left right different (agreement encode left right)
  intro i hi
  exact (mem_filter.mp hi).2

#print axioms agreement_cap_from_sets
#eval IO.eprintln "EARLY_C1_GENERIC_SET_ADAPTER_COMPLETE"

/-- Exact V7 circle-code overlap, applied to an arbitrary supplied set of
complete fibres. No assumption identifies this set with a computed filter. -/
theorem matching_set_cap (left right : Message) (different : left ≠ right)
    (good : Finset (Fin 262144))
    (hmatches : ∀ f ∈ good, fibreEncode left f = fibreEncode right f) :
    good.card ≤ 256 := by
  have subset : good ⊆ fullFibreAgreement left right := by
    intro f hf
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    intro slot
    exact congrFun (hmatches f hf) slot
  exact (card_le_card subset).trans (full_fibre_overlap_le_256 left right different)

#print axioms matching_set_cap
#eval IO.eprintln "EARLY_C1_CONCRETE_SET_CAP_COMPLETE"

theorem exact_agreement_cap (left right : Message) (different : left ≠ right) :
    (agreement fibreEncode left right).card ≤ 256 := by
  exact agreement_cap_from_sets fibreEncode 256 matching_set_cap left right different

#print axioms exact_agreement_cap
#eval IO.eprintln "EARLY_C1_AGREEMENT_CAP_COMPLETE"

/- This is the concrete optional object from the preceding committed leaf,
not a new decoder that takes its answer from a later tuple. -/
/- ENDPOINT DRAFT, inactive for cap-only preflight.
theorem identify (received : C1Received) (p : C1Messages)
    (own : 245609 ≤ (support fibreEncode (receivedFibres received) p).card) :
    earlyC1 received = some p := by
  unfold earlyC1
  exact early_eq_of_large_support fibreEncode (receivedFibres received) p 245609 256
    exact_agreement_cap c1_margin own

#print axioms identify
#eval IO.eprintln "EARLY_C1_IDENTIFICATION_COMPLETE"
-/
end AspisV8.EarlyC1Identification
