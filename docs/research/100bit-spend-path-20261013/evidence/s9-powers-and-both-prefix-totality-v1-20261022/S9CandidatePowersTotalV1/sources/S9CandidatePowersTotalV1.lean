import S9CandidateExplicitPowersArrayBridgeV1
import S9QMMulTotalCanonicalV1
import S3S9ScalarFactorKpowersReadV1

open Aeneas Aeneas.Std Result
set_option autoImplicit false

namespace AspisR1S9CandidatePowersTotalV1

abbrev CQ := AspisR1S9CandidateHelperV1.field.QM31
abbrev PQ := AspisR1S9HelperP6.field.QM31
abbrev U := Std.Usize

private abbrev candidateCanonical (x : CQ) : Prop :=
  AspisR1CurrentWide.Proof.CanonicalQM
    (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM
      (AspisR1S9CandidateHelperV1.toP6Q x))

private theorem candidate_one_map :
    AspisR1S9CandidateHelperV1.toP6Q
      AspisR1S9CandidateHelperV1.field.QM31.ONE =
    AspisR1S9HelperP6.field.QM31.ONE := by
  unfold AspisR1S9CandidateHelperV1.toP6Q
    AspisR1S9CandidateHelperV1.toP6CM
    AspisR1S9CandidateHelperV1.toP6M
    AspisR1S9CandidateHelperV1.field.QM31.ONE
    AspisR1S9HelperP6.field.QM31.ONE
  rfl

private theorem one_canonical : candidateCanonical AspisR1S9CandidateHelperV1.field.QM31.ONE := by
  change AspisR1CurrentWide.Proof.CanonicalQM
    (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM
      (AspisR1S9CandidateHelperV1.toP6Q AspisR1S9CandidateHelperV1.field.QM31.ONE))
  rw [candidate_one_map]
  change @AspisR1S9HelperP6PowerSemanticsV1.QMSemantics.canonical
    AspisR1CurrentWide.Proof.ExactQM _
    AspisR1S9HelperP6PowerSemanticsV1.currentFieldOps
    AspisR1S9HelperP6PowerSemanticsV1.currentQMSemantics
    AspisR1S9HelperP6.field.QM31.ONE
  exact @AspisR1S9HelperP6PowerSemanticsV1.QMSemantics.one_canonical
    AspisR1CurrentWide.Proof.ExactQM _
    AspisR1S9HelperP6PowerSemanticsV1.currentFieldOps
    AspisR1S9HelperP6PowerSemanticsV1.currentQMSemantics

private theorem candidate_mul_total
    (x y : CQ) (hx : candidateCanonical x) (hy : candidateCanonical y) :
    ∃ z : CQ,
      AspisR1S9CandidateHelperV1.field.QM31.mul x y = .ok z ∧
      candidateCanonical z := by
  obtain ⟨zp, hp, hcp⟩ :=
    AspisR1S9QMMulTotalCanonicalV1.concrete_qm_mul_total
      (AspisR1S9CandidateHelperV1.toP6Q x)
      (AspisR1S9CandidateHelperV1.toP6Q y) hx hy
  have hm := AspisR1S9CandidateHelperBridgeV1.map_qm_mul x y
  rw [hp] at hm
  cases hc : AspisR1S9CandidateHelperV1.field.QM31.mul x y with
  | ok z =>
      have hz : AspisR1S9CandidateHelperV1.toP6Q z = zp := by
        have : Result.ok (AspisR1S9CandidateHelperV1.toP6Q z) = Result.ok zp := by
          simpa only [AspisR1S9CandidateHelperBridgeV1.mapResult, hc] using hm
        exact Result.ok.inj this
      refine ⟨z, rfl, ?_⟩
      change AspisR1CurrentWide.Proof.CanonicalQM
        (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM
          (AspisR1S9CandidateHelperV1.toP6Q z))
      rw [hz]
      exact hcp
  | fail e =>
      simp only [hc, AspisR1S9CandidateHelperBridgeV1.mapResult] at hm
      cases hm
  | div =>
      simp only [hc, AspisR1S9CandidateHelperBridgeV1.mapResult] at hm
      cases hm

/-- The four explicit candidate multiplications are total from a canonical
seed. Their first three outputs form exactly the returned P6 `kpowers` array;
all four candidate outputs retain canonicality. -/
theorem candidate_powers4_total
    (seed : CQ) (hseed : candidateCanonical seed) :
    ∃ (q1 q2 q3 q4 : CQ) (values : Array PQ (4#usize)),
      AspisR1S9CandidateHelperV1.field.QM31.mul
        AspisR1S9CandidateHelperV1.field.QM31.ONE seed = .ok q1 ∧
      AspisR1S9CandidateHelperV1.field.QM31.mul q1 seed = .ok q2 ∧
      AspisR1S9CandidateHelperV1.field.QM31.mul q2 seed = .ok q3 ∧
      AspisR1S9CandidateHelperV1.field.QM31.mul q3 seed = .ok q4 ∧
      candidateCanonical q1 ∧ candidateCanonical q2 ∧
      candidateCanonical q3 ∧ candidateCanonical q4 ∧
      @AspisR1S9HelperP6.weights.kpowers AspisR1S9HelperP6PowerSemanticsV1.currentQMOps
        (4#usize) (AspisR1S9CandidateHelperV1.toP6Q seed) = .ok values ∧
      values.val = [
        AspisR1S9CandidateHelperV1.toP6Q AspisR1S9CandidateHelperV1.field.QM31.ONE,
        AspisR1S9CandidateHelperV1.toP6Q q1,
        AspisR1S9CandidateHelperV1.toP6Q q2,
        AspisR1S9CandidateHelperV1.toP6Q q3] ∧
      (∀ (j : U) (v : PQ), Array.index_usize values j = .ok v →
        @AspisR1S9HelperP6PowerSemanticsV1.QMSemantics.canonical
          AspisR1CurrentWide.Proof.ExactQM _
          AspisR1S9HelperP6PowerSemanticsV1.currentFieldOps
          AspisR1S9HelperP6PowerSemanticsV1.currentQMSemantics v) := by
  obtain ⟨q1, h1, hc1⟩ := candidate_mul_total
    AspisR1S9CandidateHelperV1.field.QM31.ONE seed one_canonical hseed
  obtain ⟨q2, h2, hc2⟩ := candidate_mul_total q1 seed hc1 hseed
  obtain ⟨q3, h3, hc3⟩ := candidate_mul_total q2 seed hc2 hseed
  obtain ⟨q4, h4, hc4⟩ := candidate_mul_total q3 seed hc3 hseed
  have hp6seed : @AspisR1S9HelperP6PowerSemanticsV1.QMSemantics.canonical
      AspisR1CurrentWide.Proof.ExactQM _
      AspisR1S9HelperP6PowerSemanticsV1.currentFieldOps
      AspisR1S9HelperP6PowerSemanticsV1.currentQMSemantics
      (AspisR1S9CandidateHelperV1.toP6Q seed) := hseed
  obtain ⟨values, hvalues, hlist⟩ :=
    AspisR1S9CandidateExplicitPowersArrayBridgeV1.candidate_explicit_powers4_matches_p6
      seed q1 q2 q3 q4 hp6seed h1 h2 h3 h4
  have hcan : ∀ (j : U) (v : PQ), Array.index_usize values j = .ok v →
      @AspisR1S9HelperP6PowerSemanticsV1.QMSemantics.canonical
        AspisR1CurrentWide.Proof.ExactQM _
        AspisR1S9HelperP6PowerSemanticsV1.currentFieldOps
        AspisR1S9HelperP6PowerSemanticsV1.currentQMSemantics v := by
    intro j v hread
    have hcanonical := (AspisR1S9ScalarFactorKpowersReadV1.kpowers_success_read_current
      (AspisR1S9CandidateHelperV1.toP6Q seed) values hp6seed hvalues j v hread).1
    change @AspisR1S9HelperP6PowerSemanticsV1.QMSemantics.canonical
      AspisR1CurrentWide.Proof.ExactQM _
      AspisR1S9HelperP6PowerSemanticsV1.currentFieldOps
      AspisR1S9HelperP6PowerSemanticsV1.currentQMSemantics v
    exact hcanonical
  exact ⟨q1, q2, q3, q4, values, h1, h2, h3, h4,
    hc1, hc2, hc3, hc4, hvalues, hlist, hcan⟩

#print axioms candidate_powers4_total

end AspisR1S9CandidatePowersTotalV1
