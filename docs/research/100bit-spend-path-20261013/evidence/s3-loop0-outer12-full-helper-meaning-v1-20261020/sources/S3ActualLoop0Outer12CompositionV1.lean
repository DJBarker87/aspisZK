import S3ZeroSeedMeaningV1
import S3ActualLoop1OuterWholePrefixPublicV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1GroupedPairActualFieldOpsV3.ActualLoop0Outer12Composition

open AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete
open AspisR1GroupedPairActualFieldOpsV3.SuccessPrefixComposition
open AspisR1GroupedPairActualFieldOpsV3.ZeroSeedMeaning
open AspisR1GroupedPairActualFieldOpsV3.ActualLoop1OuterPrefixPublic
open AspisR1GroupedPairActualFieldOpsV3.ActualLoop1

private theorem bind_success_inv {A B : Type} (m : Result A) (k : A → Result B)
    (v : B) (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- A successful actual grouped-pair call supplies its exact loop0 coefficient
array, proves that array canonical from the source success, and binds that
same array to the actual outer-12 run. The final conjunct is the outer loop's
source-shaped selected-prefix theorem for this same output. -/
theorem actual_grouped_success_supplies_fullpair_meaning
    (bytes : Slice Std.U8) (low : Array field.WideExact 16#usize)
    (out : field.WideExact)
    (hlow : CanonicalLow low)
    (h : weights.s2_grouped_inactive_pair actualOperations bytes low = .ok out) :
    ∃ coefficients,
      weights.s2_grouped_inactive_pair_loop0 actualOperations
        { start := 0#usize, «end» := 64#usize } bytes
        (Array.repeat 12#usize field.WideExact.ZERO) = .ok coefficients ∧
      ∃ hcoeff : CanonicalCoefficients coefficients,
        weights.s2_grouped_inactive_pair_loop1 actualOperations
          { start := 0#usize, «end» := 12#usize } low coefficients
          field.WideExact.ZERO = .ok out ∧
        Canonical out ∧ decode out = actualOuterPrefix low coefficients 12 := by
  unfold weights.s2_grouped_inactive_pair at h
  change (do
    let coefficients ← weights.s2_grouped_inactive_pair_loop0 actualOperations
      { start := 0#usize, «end» := 64#usize } bytes
      (Array.repeat 12#usize field.WideExact.ZERO)
    weights.s2_grouped_inactive_pair_loop1 actualOperations
      { start := 0#usize, «end» := 12#usize } low coefficients
      field.WideExact.ZERO) = .ok out at h
  obtain ⟨coefficients, hloop0, hloop1⟩ := bind_success_inv
    (weights.s2_grouped_inactive_pair_loop0 actualOperations
      { start := 0#usize, «end» := 64#usize } bytes
      (Array.repeat 12#usize field.WideExact.ZERO))
    (fun coefficients => weights.s2_grouped_inactive_pair_loop1 actualOperations
      { start := 0#usize, «end» := 12#usize } low coefficients
      field.WideExact.ZERO) out h
  obtain ⟨coefficients0, hzeroRun, _hmeaning, hcanonical⟩ :=
    grouped_success_implies_zero_seed_prefix bytes low out h
  have hcoeffEq : coefficients0 = coefficients := Result.ok.inj (hzeroRun.symm.trans hloop0)
  subst coefficients0
  have hcoeff : CanonicalCoefficients coefficients := by
    intro i
    have hi := hcanonical i
    simpa [CanonicalAccumulatorArray, CanonicalCoefficients] using hi
  obtain ⟨result, houter, houterCanonical, houterMeaning⟩ :=
    actual_loop1_whole_prefix low coefficients hlow hcoeff
  have hresultEq : result = out := Result.ok.inj (houter.symm.trans hloop1)
  subst result
  refine ⟨coefficients, ?_⟩
  refine ⟨hloop0, ?_⟩
  refine ⟨hcoeff, ?_⟩
  refine ⟨hloop1, ?_⟩
  change Canonical out ∧ decode out = actualOuterPrefix low coefficients 12
  exact ⟨houterCanonical, houterMeaning⟩

#print axioms actual_grouped_success_supplies_fullpair_meaning

end AspisR1GroupedPairActualFieldOpsV3.ActualLoop0Outer12Composition
