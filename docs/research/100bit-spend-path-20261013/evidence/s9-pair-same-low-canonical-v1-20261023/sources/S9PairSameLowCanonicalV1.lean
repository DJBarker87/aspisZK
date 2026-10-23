import S9PairCallerBodyPrefixV1
import S9CandidateArithmeticPrefixV1
import S9PairCallerScalarFactorCandidateMapV1
import S9PairCallerCandidateMapV1
import S9CandidateFoldMapPrimitivesV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1S9PairSameLowCanonicalV1

abbrev U := Std.Usize
abbrev PW := AspisR1S9PairCallerStepV1.field.WideExact
abbrev PQ := AspisR1S9PairCallerStepV1.field.QM31
abbrev CW := AspisR1S9CandidateHelperV1.field.WideExact
abbrev CQ := AspisR1S9CandidateHelperV1.field.QM31
abbrev mapArray {A B : Type} {N : Usize} (f : A → B) (a : Array A N) : Array B N :=
  AspisR1S9CandidateFoldMapPrimitivesV1.mapArray f a

private theorem pair_one_maps :
    AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ
      AspisR1S9PairCallerStepV1.field.QM31.ONE =
    AspisR1S9CandidateHelperV1.field.QM31.ONE := by
  unfold AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ
    AspisR1S9PairCallerStepV1.toP6Q AspisR1S9CandidateHelperV1.fromP6Q
    AspisR1S9PairCallerStepV1.field.QM31.ONE
    AspisR1S9CandidateHelperV1.field.QM31.ONE
    AspisR1S9PairCallerStepV1.toP6CM AspisR1S9CandidateHelperV1.fromP6CM
    AspisR1S9PairCallerStepV1.toP6M AspisR1S9CandidateHelperV1.fromP6M
  rfl

private theorem pair_map_make4 (q1 q2 q3 : PQ) :
    mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ
      (Array.make 4#usize [AspisR1S9PairCallerStepV1.field.QM31.ONE,q1,q2,q3]) =
    Array.make 4#usize [AspisR1S9CandidateHelperV1.field.QM31.ONE,
      AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ q1,
      AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ q2,
      AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ q3] := by
  unfold mapArray AspisR1S9CandidateFoldMapPrimitivesV1.mapArray Array.make
  simp only [pair_one_maps, List.map_cons, List.map_nil]

private theorem mapped_read_value
    (a : Array PQ 2#usize) (i : U) (x : PQ) (y : CQ)
    (hi : Array.index_usize a i = .ok x)
    (hy : Array.index_usize (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ a) i = .ok y) :
    y = AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ x := by
  have hm := AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result
    AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ a i
  rw [hi] at hm
  have hm' : Array.index_usize
      (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ a) i =
      .ok (AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ x) := by
    simpa only [AspisR1S9CandidateFoldMapPrimitivesV1.mapResult] using hm.symm
  exact Result.ok.inj (hy.symm.trans hm')

private theorem mapped_mul_value
    (x y z : PQ) (zc : CQ)
    (hp : AspisR1S9PairCallerStepV1.field.QM31.mul x y = .ok z)
    (hc : AspisR1S9CandidateHelperV1.field.QM31.mul
      (AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ x)
      (AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ y) = .ok zc) :
    zc = AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ z := by
  have hm := AspisR1S9PairCallerCandidateMapV1.pair_qm_mul_maps_to_candidate x y
  rw [hp] at hm
  change Result.ok (AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ z) =
    (AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ x).mul
      (AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ y) at hm
  exact (Result.ok.inj (hm.trans hc)).symm

/-- Canonicality of the exact Pair scalar result. The candidate prefix is
constructed on mapped inputs; its seed and first three powers are aligned to
the same Pair prefix calls before identifying the scalar Result. -/
theorem same_pair_body_low_is_canonical
    (ap0 ap1 : Array PW 4#usize) (extra : Array PQ 2#usize)
    (side : U) (iterNext : AspisR1S9PairCallerBodyPrefixV1.R)
    (weights : Array PW 4#usize)
    (flow : ControlFlow (AspisR1S9PairCallerBodyPrefixV1.R × Array PW 4#usize) (Array PW 4#usize))
    (hbody : AspisR1S9PairCallerBodyPrefixV1.pairActiveBody
      ap0 ap1 extra side iterNext weights = .ok flow)
    (hside : side.val < 2)
    (hap0 : ∀ (j : U) (x : AspisR1S9HelperP6.field.WideExact),
      Array.index_usize
        (mapArray AspisR1S9CandidateHelperV1.toP6W
          (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW ap0)) j = .ok x →
      AspisR1S9CurrentFieldOpsV1.Canonical x)
    (hap1 : ∀ (j : U) (x : AspisR1S9HelperP6.field.WideExact),
      Array.index_usize
        (mapArray AspisR1S9CandidateHelperV1.toP6W
          (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW ap1)) j = .ok x →
      AspisR1S9HighTermsTraceV1.canonicalW x)
    (hextra : ∀ (j : U) (x : AspisR1S9HelperP6.field.QM31),
      Array.index_usize
        (mapArray AspisR1S9CandidateHelperV1.toP6Q
          (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ extra)) j = .ok x →
      AspisR1CurrentWide.Proof.CanonicalQM
        (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM x)) :
    ∃ (q q1 q2 q3 unusedQ4 q4 q41 q8 q12 q16 : PQ) (low : PW),
      Array.index_usize extra side = .ok q ∧
      AspisR1S9PairCallerStepV1.field.QM31.mul
        AspisR1S9PairCallerStepV1.field.QM31.ONE q = .ok q1 ∧
      AspisR1S9PairCallerStepV1.field.QM31.mul q1 q = .ok q2 ∧
      AspisR1S9PairCallerStepV1.field.QM31.mul q2 q = .ok q3 ∧
      AspisR1S9PairCallerStepV1.field.QM31.mul q3 q = .ok unusedQ4 ∧
      Array.index_usize (Array.make 4#usize [AspisR1S9PairCallerStepV1.field.QM31.ONE,q1,q2,q3]) 2#usize = .ok q4 ∧
      AspisR1S9PairCallerStepV1.field.QM31.square q4 = .ok q41 ∧
      AspisR1S9PairCallerStepV1.field.QM31.square q41 = .ok q8 ∧
      AspisR1S9PairCallerStepV1.field.QM31.mul q8 q41 = .ok q12 ∧
      AspisR1S9PairCallerStepV1.field.QM31.square q8 = .ok q16 ∧
      AspisR1S9PairCallerStepV1.weights.Weights.scalar_factor
        (Array.make 4#usize [AspisR1S9PairCallerStepV1.field.QM31.ONE,q1,q2,q3]) ap0 = .ok low ∧
      AspisR1S9PairCallerBodyPrefixV1.pairAfterLow ap1 side iterNext weights q41 q8 q12 q16 low = .ok flow ∧
      AspisR1S9CurrentFieldOpsV1.Canonical (AspisR1S9PairCallerStepV1.toP6W low) := by
  obtain ⟨q,q1,q2,q3,unusedQ4,q4,q41,q8,q12,q16,low,
      hq,hq1,hq2,hq3,hunused,hq4,hq41,hq8,hq12,hq16,hlow,_htail⟩ :=
    AspisR1S9PairCallerBodyPrefixV1.pair_active_prefix_from_success
      ap0 ap1 extra side iterNext weights flow hbody
  obtain ⟨pfx⟩ := AspisR1S9CandidateArithmeticPrefixV1.candidate_arithmetic_prefix_total
    (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW ap0)
    (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW ap1)
    (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ extra)
    side hside hap0 hap1 hextra
  have hseed : pfx.seed = AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ q :=
    mapped_read_value extra side q pfx.seed hq pfx.seed_read
  have hpfxmul1 : AspisR1S9CandidateHelperV1.field.QM31.mul
      (AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ
        AspisR1S9PairCallerStepV1.field.QM31.ONE)
      (AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ q) = .ok pfx.q1 := by
    simpa only [pair_one_maps, hseed] using pfx.mul1
  have hq1map : pfx.q1 = AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ q1 :=
    mapped_mul_value _ _ q1 pfx.q1 hq1 hpfxmul1
  have hpfxmul2 := pfx.mul2
  rw [hq1map, hseed] at hpfxmul2
  have hq2map : pfx.q2 = AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ q2 := by
    exact mapped_mul_value _ _ q2 pfx.q2 hq2 hpfxmul2
  have hpfxmul3 := pfx.mul3
  rw [hq2map, hseed] at hpfxmul3
  have hq3map : pfx.q3 = AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ q3 := by
    exact mapped_mul_value _ _ q3 pfx.q3 hq3 hpfxmul3
  have hscalarMap := AspisR1S9PairCallerScalarFactorCandidateMapV1.pair_scalar_factor_maps_to_candidate
    (Array.make 4#usize [AspisR1S9PairCallerStepV1.field.QM31.ONE,q1,q2,q3]) ap0
  rw [hlow] at hscalarMap
  have harray : AspisR1S9PairCallerScalarFactorCandidateMapV1.mapArray
      AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ
      (Array.make 4#usize [AspisR1S9PairCallerStepV1.field.QM31.ONE,q1,q2,q3]) =
      Array.make 4#usize [AspisR1S9CandidateHelperV1.field.QM31.ONE,pfx.q1,pfx.q2,pfx.q3] := by
    change mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ
      (Array.make 4#usize [AspisR1S9PairCallerStepV1.field.QM31.ONE,q1,q2,q3]) = _
    rw [pair_map_make4, hq1map, hq2map, hq3map]
  rw [harray, pfx.scalar] at hscalarMap
  have hlowMap : AspisR1S9PairCallerCandidateMapV1.pairToCandidateW low = pfx.low :=
    Result.ok.inj hscalarMap
  have hcanonical := pfx.low_canonical
  have hcarrier : AspisR1S9CandidateHelperV1.toP6W
      (AspisR1S9PairCallerCandidateMapV1.pairToCandidateW low) =
      AspisR1S9PairCallerStepV1.toP6W low :=
    AspisR1S9PairCallerCandidateMapV1.candidateToP6_pairToCandidateW low
  change AspisR1S9CurrentFieldOpsV1.Canonical
    (AspisR1S9CandidateHelperV1.toP6W pfx.low) at hcanonical
  rw [← hlowMap, hcarrier] at hcanonical
  exact ⟨q,q1,q2,q3,unusedQ4,q4,q41,q8,q12,q16,low,
    hq,hq1,hq2,hq3,hunused,hq4,hq41,hq8,hq12,hq16,hlow,_htail,hcanonical⟩

#print axioms same_pair_body_low_is_canonical
end AspisR1S9PairSameLowCanonicalV1
