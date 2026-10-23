import S9ActualWeightsNewExtraCurrentCanonicalV3
import S9PairCallerCandidateMapV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ConstructorPairExtraContractV3
open AspisR1S9ActualWeightsNewExtraCurrentCanonicalV3
open AspisR1S9CandidateFoldMapPrimitivesV1

def pairExtra (w : AspisR1S9ActualWeightsNewBoxNewV3.Weights) :=
  mapArray candidateToPairQM w.extra

def helperExtra (w : AspisR1S9ActualWeightsNewBoxNewV3.Weights) :=
  mapArray AspisR1S9CandidateHelperV1.toP6Q
    (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ (pairExtra w))

theorem current_extra_map (w : AspisR1S9ActualWeightsNewBoxNewV3.Weights) :
    mapArray AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM (helperExtra w) =
      mapArray candidateToCurrentQM w.extra := by
  apply Subtype.ext
  simp only [mapArray, helperExtra, pairExtra, List.map_map, Function.comp_def]
  congr 1

theorem constructor_v3_extra_supplies_pair_contract
    (variant : AspisR1S9ActualWeightsNewBoxNewV3.Variant)
    (alpha : Array AspisR1S9ActualWeightsNewBoxNewV3.field.QM31 10#usize)
    (z : Array AspisR1S9ActualWeightsNewBoxNewV3.circle.SecureCirclePoint 2#usize)
    (w : AspisR1S9ActualWeightsNewBoxNewV3.Weights)
    (hnew : AspisR1S9ActualWeightsNewBoxNewV3.weights_new variant alpha z =
      .ok (core.result.Result.Ok w))
    (halpha : ∀ (i : Usize) (q : AspisR1S9PairCallerStepV1.field.QM31),
      Array.index_usize (mapArray candidateToPairQM alpha) i = .ok q →
      AspisR1CurrentWide.Proof.CanonicalQM
        (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM
          (AspisR1S9PairCallerStepV1.toP6Q q))) :
    ∀ (j : Usize) (v : AspisR1S9HelperP6.field.QM31),
      Array.index_usize (helperExtra w) j = .ok v →
      AspisR1CurrentWide.Proof.CanonicalQM
        (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM v) := by
  obtain ⟨q8,q9,h8,h9,hextra,hcanonical⟩ :=
    weights_new_extra_current_fullread_canonical_v3 variant alpha z w hnew halpha
  intro j v hread
  have hm := mapArray_index_result
    AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM (helperExtra w) j
  rw [hread] at hm
  simp only [mapResult] at hm
  rw [current_extra_map] at hm
  exact hcanonical j _ hm.symm

#print axioms current_extra_map
#print axioms constructor_v3_extra_supplies_pair_contract
end AspisR1S9ConstructorPairExtraContractV3
