import AspisR1S9CandidateHelperV1.Funs
import S9CandidateHelperOperationBridgeV1
import S3KpowersTotalConstructiveV1
import KpowersP6SuccessTraceV1
import KpowersP6PowerSemanticsV1
import S4FromFnP6FourTraceV1
import S3S9ConcreteFieldOpsV1

open Aeneas Aeneas.Std Result
set_option autoImplicit false

namespace AspisR1S9CandidateExplicitPowersArrayBridgeV1

open AspisR1S9CandidateHelperV1
open AspisR1S9HelperP6
open AspisR1S9HelperP6PowerSemanticsV1
open AspisR1S9HelperP6TraceV1
open AspisR1FromFnP6Generated

abbrev CQ := AspisR1S9CandidateHelperV1.field.QM31
abbrev PQ := AspisR1S9HelperP6.field.QM31

/-- Canonicality predicate from the accepted current proof carrier, stated
without projecting through an ambient FieldOps instance. -/
abbrev CanonicalQ (x : PQ) :=
  AspisR1CurrentWide.Proof.CanonicalQM
    (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM x)

private theorem candidate_toP6_one :
    AspisR1S9CandidateHelperV1.toP6Q
      AspisR1S9CandidateHelperV1.field.QM31.ONE =
        AspisR1S9HelperP6.field.QM31.ONE := by
  unfold AspisR1S9CandidateHelperV1.toP6Q
    AspisR1S9CandidateHelperV1.toP6CM
    AspisR1S9CandidateHelperV1.toP6M
    AspisR1S9CandidateHelperV1.field.QM31.ONE
    AspisR1S9HelperP6.field.QM31.ONE
  rfl

private theorem candidate_mul_current
    (x y z : CQ)
    (h : AspisR1S9CandidateHelperV1.field.QM31.mul x y = .ok z) :
    @AspisR1S9HelperP6.FieldOps.qmMul currentQMOps
      (AspisR1S9CandidateHelperV1.toP6Q x)
      (AspisR1S9CandidateHelperV1.toP6Q y) =
        .ok (AspisR1S9CandidateHelperV1.toP6Q z) := by
  have hmap := AspisR1S9CandidateHelperBridgeV1.map_qm_mul x y
  rw [h] at hmap
  have hc : @AspisR1S9HelperP6.FieldOps.qmMul
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      (AspisR1S9CandidateHelperV1.toP6Q x)
      (AspisR1S9CandidateHelperV1.toP6Q y) =
        .ok (AspisR1S9CandidateHelperV1.toP6Q z) := by
    simpa [AspisR1S9CandidateHelperBridgeV1.mapResult] using hmap.symm
  calc
    @AspisR1S9HelperP6.FieldOps.qmMul currentQMOps
        (AspisR1S9CandidateHelperV1.toP6Q x)
        (AspisR1S9CandidateHelperV1.toP6Q y) =
      @AspisR1S9HelperP6.FieldOps.qmMul
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (AspisR1S9CandidateHelperV1.toP6Q x)
        (AspisR1S9CandidateHelperV1.toP6Q y) := by
          symm
          exact AspisR1S9ConcreteFieldOpsV1.concrete_qmMul_is_current _ _
    _ = .ok (AspisR1S9CandidateHelperV1.toP6Q z) := hc

/-- The three visible products in the candidate's explicit low-power array
are exactly the first three P6 callback outputs under the same concrete
`qmMul`. The final fourth candidate multiplication is retained as an input
fact to preserve the candidate source schedule, although it is not an array
entry. This theorem does not identify Rust `from_fn` with the P6 model; it
compares the candidate's explicit output values with an independently
successful retained P6 `kpowers` result. -/
theorem candidate_explicit_powers4_matches_p6
    (seed q1 q2 q3 q4 : CQ)
    (hseed : @AspisR1S9HelperP6PowerSemanticsV1.QMSemantics.canonical
      AspisR1CurrentWide.Proof.ExactQM _
      AspisR1S9HelperP6PowerSemanticsV1.currentFieldOps
      AspisR1S9HelperP6PowerSemanticsV1.currentQMSemantics
      (AspisR1S9CandidateHelperV1.toP6Q seed))
    (hmul1 : AspisR1S9CandidateHelperV1.field.QM31.mul
      AspisR1S9CandidateHelperV1.field.QM31.ONE seed = .ok q1)
    (hmul2 : AspisR1S9CandidateHelperV1.field.QM31.mul q1 seed = .ok q2)
    (hmul3 : AspisR1S9CandidateHelperV1.field.QM31.mul q2 seed = .ok q3)
    (hmul4 : AspisR1S9CandidateHelperV1.field.QM31.mul q3 seed = .ok q4) :
    ∃ p6Values : Array PQ (4#usize),
      @weights.kpowers currentQMOps (4#usize)
        (AspisR1S9CandidateHelperV1.toP6Q seed) = .ok p6Values ∧
      p6Values.val = [
        AspisR1S9CandidateHelperV1.toP6Q
          AspisR1S9CandidateHelperV1.field.QM31.ONE,
        AspisR1S9CandidateHelperV1.toP6Q q1,
        AspisR1S9CandidateHelperV1.toP6Q q2,
        AspisR1S9CandidateHelperV1.toP6Q q3] := by
  letI : AspisR1S9HelperP6.FieldOps := currentQMOps
  obtain ⟨p6Values, hp6⟩ :=
    AspisR1S3KpowersTotalConstructiveV1.kpowers_success_of_canonical_seed
      (AspisR1S9CandidateHelperV1.toP6Q seed) hseed
  have h1 := candidate_mul_current
    AspisR1S9CandidateHelperV1.field.QM31.ONE seed q1 hmul1
  rw [candidate_toP6_one] at h1
  have h2 := candidate_mul_current q1 seed q2 hmul2
  have h3 := candidate_mul_current q2 seed q3 hmul3
  have _h4 := candidate_mul_current q3 seed q4 hmul4
  obtain ⟨final, htrace⟩ :=
    AspisR1S9HelperP6TraceV1.kpowers_success_trace hp6
  let cb := weights.kpowers.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
    (4#usize)
  obtain ⟨v0, v1, v2, v3, s1, s2, s3, s4,
    hvalues, hstep0, hstep1, hstep2, hstep3, _hfinal⟩ :=
    AspisR1FromFnP6Generated.statefulFromFnTrace_four_calls
      cb ((AspisR1S9HelperP6.field.QM31.ONE, AspisR1S9CandidateHelperV1.toP6Q seed), 0#usize) htrace
  have hcanOne : @AspisR1S9HelperP6PowerSemanticsV1.QMSemantics.canonical
      AspisR1CurrentWide.Proof.ExactQM _ currentQMOps currentQMSemantics AspisR1S9HelperP6.field.QM31.ONE := by
    change @AspisR1S9HelperP6PowerSemanticsV1.QMSemantics.canonical
      AspisR1CurrentWide.Proof.ExactQM _
      AspisR1S9HelperP6PowerSemanticsV1.currentFieldOps currentQMSemantics AspisR1S9HelperP6.field.QM31.ONE
    exact @AspisR1S9HelperP6PowerSemanticsV1.QMSemantics.one_canonical
      AspisR1CurrentWide.Proof.ExactQM _
      AspisR1S9HelperP6PowerSemanticsV1.currentFieldOps currentQMSemantics
  obtain ⟨p1, hp1mul, _hp1can, _hp1dec, hv0, hs1⟩ :=
    AspisR1S9HelperP6PowerSemanticsV1.kpowers_step_semantic
      (sem := currentQMSemantics) hcanOne hseed hstep0
  have hp1 : p1 = AspisR1S9CandidateHelperV1.toP6Q q1 :=
    Result.ok.inj (hp1mul.symm.trans h1)
  have hv0' : v0 = AspisR1S9HelperP6.field.QM31.ONE := hv0
  have hstep1' := hstep1
  change fnMutStep cb (s1.1, s1.2) 1 = .ok (v1, s2) at hstep1'
  rw [hs1] at hstep1'
  obtain ⟨p2, hp2mul, _hp2can, _hp2dec, hv1, hs2⟩ :=
    AspisR1S9HelperP6PowerSemanticsV1.kpowers_step_semantic
      (sem := currentQMSemantics) _hp1can hseed hstep1'
  have hp2 : p2 = AspisR1S9CandidateHelperV1.toP6Q q2 := by
    rw [hp1] at hp2mul
    exact Result.ok.inj (hp2mul.symm.trans h2)
  have hv1' : v1 = AspisR1S9CandidateHelperV1.toP6Q q1 := by
    rw [hv1, hp1]
  have hstep2' := hstep2
  change fnMutStep cb (s2.1, s2.2) 2 = .ok (v2, s3) at hstep2'
  rw [hs2] at hstep2'
  obtain ⟨p3, hp3mul, _hp3can, _hp3dec, hv2, hs3⟩ :=
    AspisR1S9HelperP6PowerSemanticsV1.kpowers_step_semantic
      (sem := currentQMSemantics) _hp2can hseed hstep2'
  have hp3 : p3 = AspisR1S9CandidateHelperV1.toP6Q q3 := by
    rw [hp2] at hp3mul
    exact Result.ok.inj (hp3mul.symm.trans h3)
  have hv2' : v2 = AspisR1S9CandidateHelperV1.toP6Q q2 := by
    rw [hv2, hp2]
  have hstep3' := hstep3
  change fnMutStep cb (s3.1, s3.2) 3 = .ok (v3, s4) at hstep3'
  rw [hs3] at hstep3'
  obtain ⟨_p4, _hp4mul, _hp4can, _hp4dec, hv3, _hs4⟩ :=
    AspisR1S9HelperP6PowerSemanticsV1.kpowers_step_semantic
      (sem := currentQMSemantics) _hp3can hseed hstep3'
  have hv3' : v3 = AspisR1S9CandidateHelperV1.toP6Q q3 := by
    rw [hv3, hp3]
  have hvalues' : p6Values.val = [
      AspisR1S9CandidateHelperV1.toP6Q AspisR1S9CandidateHelperV1.field.QM31.ONE,
      AspisR1S9CandidateHelperV1.toP6Q q1,
      AspisR1S9CandidateHelperV1.toP6Q q2,
      AspisR1S9CandidateHelperV1.toP6Q q3] := by
    rw [hvalues, hv0', hv1', hv2', hv3', candidate_toP6_one]
  exact ⟨p6Values, hp6, hvalues'⟩

#print axioms candidate_explicit_powers4_matches_p6

end AspisR1S9CandidateExplicitPowersArrayBridgeV1
