import S9PairProjectionTrace4V1
import S9PairOutputReadCanonicalV1
import Query31ArrayReadback

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9PairProjectionLoopDotV1
open AspisR1S9PairCallerStepV1

abbrev U := Std.Usize
abbrev R := core.ops.range.Range U
abbrev W := Array field.WideExact (7#usize)
abbrev Canonical := AspisR1S9PairProjectionDotAtV1.Canonical
abbrev decode := AspisR1S9PairProjectionDotAtV1.decode

/-- A successful four-iteration projection loop accumulates the four actual
field/coefficient products into cell 4. Coefficient canonicality is derived
from the same successful public Pair helper result, rather than assumed for
its output. -/
theorem projection_loop_success_dot4
    (ap0 ap1 : AspisR1S9PairOutputReadCanonicalV1.PairW)
    (extra : Array AspisR1S9PairOutputReadCanonicalV1.PairQ (2#usize))
    (libra : Array field.WideExact (4#usize))
    (f : Slice U8) (initial output : W)
    (hpair : weights.factored_s2_libra_weights ap0 ap1 extra = .ok libra)
    (hp0 : ∀ (j : U) (x : AspisR1S9PairOutputReadCanonicalV1.P6W),
      Array.index_usize (AspisR1S9PairOutputReadCanonicalV1.mapArray
        AspisR1S9PairOutputReadCanonicalV1.ToP6W
        (AspisR1S9PairOutputReadCanonicalV1.mapArray
          AspisR1S9PairOutputReadCanonicalV1.PairMapW ap0)) j = .ok x →
      AspisR1S9PairOutputReadCanonicalV1.Canonical x)
    (hap1 : ∀ (j : U) (x : AspisR1S9PairOutputReadCanonicalV1.P6W),
      Array.index_usize (AspisR1S9PairOutputReadCanonicalV1.mapArray
        AspisR1S9PairOutputReadCanonicalV1.ToP6W
        (AspisR1S9PairOutputReadCanonicalV1.mapArray
          AspisR1S9PairOutputReadCanonicalV1.PairMapW ap1)) j = .ok x →
      AspisR1S9HighTermsTraceV1.canonicalW x)
    (hextra : ∀ (j : U) (x : AspisR1S9CandidateHelperV1.field.QM31),
      Array.index_usize (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
        AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ extra) j = .ok x →
      AspisR1S9CandidateHighArraySemanticsV1.CanonicalP6
        (AspisR1S9CandidateHelperV1.toP6Q x))
    (hinitial : ∀ x, Array.index_usize initial 4#usize = .ok x → Canonical x)
    (hloop : AspisR1S9PairProjectionTrace4V1.projectionLoop f libra initial = .ok output) :
    ∃ old v0 c0 v1 c1 v2 c2 v3 c3,
      Array.index_usize initial 4#usize = .ok old ∧
      weights.field f 0#usize = .ok v0 ∧ Array.index_usize libra 0#usize = .ok c0 ∧
      weights.field f 1#usize = .ok v1 ∧ Array.index_usize libra 1#usize = .ok c1 ∧
      weights.field f 2#usize = .ok v2 ∧ Array.index_usize libra 2#usize = .ok c2 ∧
      weights.field f 3#usize = .ok v3 ∧ Array.index_usize libra 3#usize = .ok c3 ∧
      (∃ final, Array.index_usize output 4#usize = .ok final ∧ Canonical final ∧
        decode final = (((decode old + decode v0 * decode c0) +
          decode v1 * decode c1) + decode v2 * decode c2) + decode v3 * decode c3) := by
  obtain ⟨tr⟩ :=
    AspisR1S9PairProjectionTrace4V1.loop_success_extracts_projection_trace4
      f libra initial output hloop
  have hlibra : ∀ j coef, Array.index_usize libra j = .ok coef → Canonical coef := by
    intro j coef hread
    exact AspisR1S9PairOutputReadCanonicalV1.pair_public_output_read_canonical
      ap0 ap1 extra libra hpair hp0 hap1 hextra j coef hread
  obtain ⟨old0, v0, c0, total0, hold0, hfield0, hcoef0, hupdate0,
    hcanV0, hcanT0, hdot0⟩ :=
    AspisR1S9PairProjectionDotAtV1.continued_projection_dot_step_at
      f libra AspisR1S9PairProjectionTrace4V1.range0
      AspisR1S9PairProjectionTrace4V1.range1 0#usize initial tr.p1
      AspisR1S9PairProjectionTrace4V1.next_range0 (hinitial) hlibra tr.hbody0
  have hdot0' := hdot0
  change decode total0 = decode old0 + decode v0 * decode c0 at hdot0'
  have hread1 := AspisR1PublicPreparation.Query31SourceSchedule.update_readback
    initial 4#usize total0 (by decide) tr.p1 hupdate0
  have hparts1 : ∀ x, Array.index_usize tr.p1 4#usize = .ok x → Canonical x := by
    intro x hx
    have heq : x = total0 := Result.ok.inj (hx.symm.trans hread1)
    rw [heq]
    exact hcanT0
  obtain ⟨old1, v1, c1, total1, hold1, hfield1, hcoef1, hupdate1,
    hcanV1, hcanT1, hdot1⟩ :=
    AspisR1S9PairProjectionDotAtV1.continued_projection_dot_step_at
      f libra AspisR1S9PairProjectionTrace4V1.range1
      AspisR1S9PairProjectionTrace4V1.range2 1#usize tr.p1 tr.p2
      AspisR1S9PairProjectionTrace4V1.next_range1 hparts1 hlibra tr.hbody1
  have hdot1' := hdot1
  change decode total1 = decode old1 + decode v1 * decode c1 at hdot1'
  have hs1 : old1 = total0 := Result.ok.inj (hold1.symm.trans hread1)
  have hread2 := AspisR1PublicPreparation.Query31SourceSchedule.update_readback
    tr.p1 4#usize total1 (by decide) tr.p2 hupdate1
  have hparts2 : ∀ x, Array.index_usize tr.p2 4#usize = .ok x → Canonical x := by
    intro x hx
    have heq : x = total1 := Result.ok.inj (hx.symm.trans hread2)
    rw [heq]
    exact hcanT1
  obtain ⟨old2, v2, c2, total2, hold2, hfield2, hcoef2, hupdate2,
    hcanV2, hcanT2, hdot2⟩ :=
    AspisR1S9PairProjectionDotAtV1.continued_projection_dot_step_at
      f libra AspisR1S9PairProjectionTrace4V1.range2
      AspisR1S9PairProjectionTrace4V1.range3 2#usize tr.p2 tr.p3
      AspisR1S9PairProjectionTrace4V1.next_range2 hparts2 hlibra tr.hbody2
  have hdot2' := hdot2
  change decode total2 = decode old2 + decode v2 * decode c2 at hdot2'
  have hs2 : old2 = total1 := Result.ok.inj (hold2.symm.trans hread2)
  have hread3 := AspisR1PublicPreparation.Query31SourceSchedule.update_readback
    tr.p2 4#usize total2 (by decide) tr.p3 hupdate2
  have hparts3 : ∀ x, Array.index_usize tr.p3 4#usize = .ok x → Canonical x := by
    intro x hx
    have heq : x = total2 := Result.ok.inj (hx.symm.trans hread3)
    rw [heq]
    exact hcanT2
  obtain ⟨old3, v3, c3, total3, hold3, hfield3, hcoef3, hupdate3,
    hcanV3, hcanT3, hdot3⟩ :=
    AspisR1S9PairProjectionDotAtV1.continued_projection_dot_step_at
      f libra AspisR1S9PairProjectionTrace4V1.range3
      AspisR1S9PairProjectionTrace4V1.range4 3#usize tr.p3 output
      AspisR1S9PairProjectionTrace4V1.next_range3 hparts3 hlibra tr.hbody3
  have hdot3' := hdot3
  change decode total3 = decode old3 + decode v3 * decode c3 at hdot3'
  have hs3 : old3 = total2 := Result.ok.inj (hold3.symm.trans hread3)
  have hfinal := AspisR1PublicPreparation.Query31SourceSchedule.update_readback
    tr.p3 4#usize total3 (by decide) output hupdate3
  refine ⟨old0, v0, c0, v1, c1, v2, c2, v3, c3,
    hold0, hfield0, hcoef0, hfield1, hcoef1, hfield2, hcoef2, hfield3, hcoef3,
    total3, hfinal, hcanT3, ?_⟩
  calc
    decode total3 = decode old3 + decode v3 * decode c3 := hdot3'
    _ = decode total2 + decode v3 * decode c3 := by rw [hs3]
    _ = (decode old2 + decode v2 * decode c2) + decode v3 * decode c3 := by rw [hdot2']
    _ = ((decode old1 + decode v1 * decode c1) + decode v2 * decode c2) +
        decode v3 * decode c3 := by rw [hs2, hdot1']
    _ = (((decode old0 + decode v0 * decode c0) + decode v1 * decode c1) +
        decode v2 * decode c2) + decode v3 * decode c3 := by rw [hs1, hdot0']

#print axioms projection_loop_success_dot4
end AspisR1S9PairProjectionLoopDotV1
