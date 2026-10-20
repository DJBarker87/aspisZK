import S3ActualLoop0Outer12CompositionV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1GroupedPairActualFieldOpsV3.ActualLoop0Outer12PrefixRetention

open AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete
open AspisR1GroupedPairActualFieldOpsV3.ActualLoop0Outer12Composition
open AspisR1GroupedPairActualFieldOpsV3.SuccessPrefixComposition
open AspisR1GroupedPairActualFieldOpsV3.ZeroSeedMeaning
open AspisR1GroupedPairActualFieldOpsV3.ActualLoop1OuterPrefixPublic
open AspisR1GroupedPairActualFieldOpsV3.ActualLoop1

/-- The successful helper's parser-backed coefficient meaning survives the
loop0/outer12 composition. Both loops and the prefix witness refer to the
same coefficient array returned by the actual source helper. -/
theorem actual_grouped_success_supplies_prefix_and_outer_meaning
    (bytes : Slice Std.U8) (low : Array field.WideExact 16#usize)
    (out : field.WideExact)
    (hlow : CanonicalLow low)
    (h : weights.s2_grouped_inactive_pair actualOperations bytes low = .ok out) :
    ∃ coefficients,
      weights.s2_grouped_inactive_pair_loop0 actualOperations
        { start := 0#usize, «end» := 64#usize } bytes
        (Array.repeat 12#usize field.WideExact.ZERO) = .ok coefficients ∧
      DecodedMeaning coefficients
        (PrefixMeaning (successfulInput bytes low out h) (fun _ => 0) 64) ∧
      CanonicalCoefficients coefficients ∧
      weights.s2_grouped_inactive_pair_loop1 actualOperations
        { start := 0#usize, «end» := 12#usize } low coefficients
        field.WideExact.ZERO = .ok out ∧
      Canonical out ∧ decode out = actualOuterPrefix low coefficients 12 := by
  obtain ⟨coefficients, hloop0, hcoeff, hloop1, hcanonical, houter⟩ :=
    actual_grouped_success_supplies_fullpair_meaning bytes low out hlow h
  obtain ⟨coefficients0, hzero, hprefix, _hcanonical0⟩ :=
    grouped_success_implies_zero_seed_prefix bytes low out h
  have hcoefficients : coefficients0 = coefficients :=
    Result.ok.inj (hzero.symm.trans hloop0)
  subst coefficients0
  exact ⟨coefficients, hloop0, hprefix, hcoeff, hloop1, hcanonical, houter⟩

#print axioms actual_grouped_success_supplies_prefix_and_outer_meaning

end AspisR1GroupedPairActualFieldOpsV3.ActualLoop0Outer12PrefixRetention
