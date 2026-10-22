import S9CandidateScalarFactorFoldTransportV1
import S3ScalarFactorExtractedFoldTotalV1
import S9TwoCallScalarMeaningV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9CandidateScalarFactorTotalV1

abbrev U := Std.Usize
abbrev CQ := AspisR1S9CandidateHelperV1.field.QM31
abbrev CW := AspisR1S9CandidateHelperV1.field.WideExact
abbrev PW := AspisR1S9HelperP6.field.WideExact
abbrev PQ := AspisR1S9HelperP6.field.QM31
abbrev mapArray {A B : Type} {N : Usize} (f : A → B) (a : Array A N) : Array B N :=
  AspisR1S9CandidateFoldMapPrimitivesV1.mapArray f a

/-- Canonical mapped caller cells and canonical mapped powers reads suffice
for the actual generated candidate scalar call to succeed. Its returned value
maps to the exact selected P6 result; no successful call is assumed. -/
theorem candidate_scalar_factor_total_and_maps
    (f : Array CQ (4#usize)) (p : Array CW (4#usize))
    (hp : ∀ (j : U) (x : PW),
      Array.index_usize (mapArray AspisR1S9CandidateHelperV1.toP6W p) j = .ok x →
      AspisR1S9CurrentFieldOpsV1.Canonical x)
    (hf : ∀ (j : U) (x : PQ),
      Array.index_usize (mapArray AspisR1S9CandidateHelperV1.toP6Q f) j = .ok x →
      AspisR1CurrentWide.Proof.CanonicalQM
        (AspisR1S9GeneratedWideMulQM31V2.toQM x)) :
    ∃ low : CW,
      AspisR1S9CandidateHelperV1.weights.Weights.scalar_factor f p = .ok low ∧
      @AspisR1S9HelperP6.weights.Weights.scalar_factor
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (mapArray AspisR1S9CandidateHelperV1.toP6Q f)
        (mapArray AspisR1S9CandidateHelperV1.toP6W p) =
        .ok (AspisR1S9CandidateHelperV1.toP6W low) := by
  obtain ⟨p6low, hinstalled⟩ :=
    AspisR1S3ScalarFactorExtractedFoldTotalV1.scalar_factor_total_with_extracted_fold
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      (mapArray AspisR1S9CandidateHelperV1.toP6W p)
      (mapArray AspisR1S9CandidateHelperV1.toP6Q f) hp hf
  have hp6 : @AspisR1S9HelperP6.weights.Weights.scalar_factor
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      (mapArray AspisR1S9CandidateHelperV1.toP6Q f)
      (mapArray AspisR1S9CandidateHelperV1.toP6W p) = .ok p6low := by
    rw [AspisR1S9TwoCallScalarMeaningV2.concrete_factor_ops_eq] at hinstalled
    exact hinstalled
  have hmap :=
    AspisR1S9CandidateScalarFactorFoldTransportV1.candidate_scalar_factor_maps_to_p6 f p
  rw [hp6] at hmap
  cases hcandidate : AspisR1S9CandidateHelperV1.weights.Weights.scalar_factor f p with
  | ok low =>
      have hvalue : AspisR1S9CandidateHelperV1.toP6W low = p6low := by
        have heq : .ok (AspisR1S9CandidateHelperV1.toP6W low) = (Result.ok p6low) := by
          simpa only [AspisR1S9CandidateFoldMapPrimitivesV1.mapResult, hcandidate] using hmap
        exact Result.ok.inj heq
      refine ⟨low, rfl, ?_⟩
      calc
        @AspisR1S9HelperP6.weights.Weights.scalar_factor
            AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
            (mapArray AspisR1S9CandidateHelperV1.toP6Q f)
            (mapArray AspisR1S9CandidateHelperV1.toP6W p) = .ok p6low := hp6
        _ = .ok (AspisR1S9CandidateHelperV1.toP6W low) := by
          exact congrArg Result.ok hvalue.symm
  | fail e =>
      simp only [hcandidate, AspisR1S9CandidateFoldMapPrimitivesV1.mapResult] at hmap
      cases hmap
  | div =>
      simp only [hcandidate, AspisR1S9CandidateFoldMapPrimitivesV1.mapResult] at hmap
      cases hmap

#print axioms candidate_scalar_factor_total_and_maps

end AspisR1S9CandidateScalarFactorTotalV1
