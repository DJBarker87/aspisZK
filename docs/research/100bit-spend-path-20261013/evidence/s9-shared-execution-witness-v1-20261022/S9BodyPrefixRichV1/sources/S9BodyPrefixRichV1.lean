import S9HighPowerPrefixSemanticsV1
import S9ConcreteScalarCallSemanticsV1
import S9HighTermsTraceV1
import S9AfterScalarTermSumsV2
import S9AfterSumsTailDispatchV1
import S9SideZeroTailRootV1
import S9ArrayWriteScheduleRootV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1S9BodyPrefixSemanticsV1

open AspisR1S9HelperP6

local instance concreteOps : FieldOps :=
  AspisR1S9ConcreteFieldOpsV1.concreteFieldOps

abbrev W := Array field.WideExact (4#usize)
abbrev Q := field.QM31
abbrev U := Std.Usize
abbrev canonical := AspisR1S9CurrentFieldOpsV1.Canonical
abbrev decode := AspisR1S9CurrentFieldOpsV1.decode
abbrev cells (a : W) (j : Fin 4) := AspisR1.S9ArrayWriteScheduleRootV1.cells a j

private theorem bind_success_inv {α β : Type}
    (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- The active body prefix supplies the exact scalar result, selected high-term
trace, and ordered sums before the branch-specific tail. -/
theorem active_body_prefix_rich
    (ap0 ap1 : W) (extra : Array Q (2#usize))
    (side : U) (iterNext : core.ops.range.Range U) (weights0 : W)
    (flow : ControlFlow (core.ops.range.Range U × W) W)
    (hactive : AspisR1S9FactoredLoopBodyShapeV3.activeBody
      ap0 ap1 extra side iterNext weights0 = .ok flow)
    (hp0 : ∀ (j : U) (x : field.WideExact),
      Array.index_usize ap0 j = .ok x → canonical x)
    (hp1 : ∀ (j : U) (x : field.WideExact),
      Array.index_usize ap1 j = .ok x → canonical x)
    (hextra : ∀ (j : U) (x : Q),
      Array.index_usize extra j = .ok x →
      AspisR1S9HighPowerPrefixSemanticsV1.CanonicalQ x) :
    ∃ (q : Q) (q1 : Array Q (4#usize))
      (q2 q4 q8 q12 q16 : Q) (low : field.WideExact)
      (high : Array Q (4#usize)) (terms : W)
      (state : (W × Array Q (4#usize)) × U)
      (hterms : AspisR1S9HighTermsTraceV1.HighTermsFour ap1 high)
      (we we1 first2 we2 first3 we3 all : field.WideExact),
      Array.index_usize extra side = .ok q ∧
      @weights.kpowers AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (4#usize) q = .ok q1 ∧
      Array.index_usize q1 2#usize = .ok q2 ∧
      @FieldOps.qmSquare AspisR1S9ConcreteFieldOpsV1.concreteFieldOps q2 = .ok q4 ∧
      @FieldOps.qmSquare AspisR1S9ConcreteFieldOpsV1.concreteFieldOps q4 = .ok q8 ∧
      @FieldOps.qmMul AspisR1S9ConcreteFieldOpsV1.concreteFieldOps q8 q4 = .ok q12 ∧
      @FieldOps.qmSquare AspisR1S9ConcreteFieldOpsV1.concreteFieldOps q8 = .ok q16 ∧
      @weights.Weights.scalar_factor AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        q1 ap0 = .ok low ∧
      AspisR1S9TwoCallScalarMeaningV2.ScalarMeaning ap0 q1 low q ∧
      AspisR1S9CurrentFieldOpsV1.Canonical low ∧
      @AspisR1S9TwoCallScalarMeaningV2.afterScalar
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps ap0 ap1 extra side
        iterNext weights0 q4 q8 q12 q16 low = .ok flow ∧
      high = Array.make 4#usize [field.QM31.ONE, q4, q8, q12] ∧
      (∀ (j : U) (z : Q), Array.index_usize high j = .ok z →
        AspisR1CurrentWide.Proof.CanonicalQM
          (AspisR1S9GeneratedWideMulQM31V2.toQM z)) ∧
      (∀ (j : U) (z : Q), Array.index_usize high j = .ok z →
        AspisR1S9HighPowerPrefixSemanticsV1.decodeQ z =
          AspisR1S9HighPowerPrefixSemanticsV1.decodeQ q ^ (4 * j.val)) ∧
      AspisR1S9HighPowerPrefixSemanticsV1.CanonicalQ q16 ∧
      AspisR1S9HighPowerPrefixSemanticsV1.decodeQ q16 =
        AspisR1S9HighPowerPrefixSemanticsV1.decodeQ q ^ 16 ∧
      @core.array.from_fn field.WideExact
        weights.factored_s2_libra_weights.closure
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (4#usize)
        weights.factored_s2_libra_weights.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
        (ap1, high) = .ok (terms, state) ∧
      Array.index_usize terms 0#usize = .ok we ∧
      Array.index_usize terms 1#usize = .ok we1 ∧
      @field.WideExact.add AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        we we1 = .ok first2 ∧
      Array.index_usize terms 2#usize = .ok we2 ∧
      @field.WideExact.add AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        first2 we2 = .ok first3 ∧
      Array.index_usize terms 3#usize = .ok we3 ∧
      @field.WideExact.add AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        first3 we3 = .ok all ∧
      AspisR1S9CurrentFieldOpsV1.Canonical first2 ∧
      AspisR1S9CurrentFieldOpsV1.decode first2 =
        AspisR1S9AfterScalarTermSumsV2.decW we + AspisR1S9AfterScalarTermSumsV2.decW we1 ∧
      AspisR1S9CurrentFieldOpsV1.Canonical first3 ∧
      AspisR1S9CurrentFieldOpsV1.decode first3 =
        AspisR1S9CurrentFieldOpsV1.decode first2 + AspisR1S9AfterScalarTermSumsV2.decW we2 ∧
      AspisR1S9CurrentFieldOpsV1.Canonical all ∧
      AspisR1S9CurrentFieldOpsV1.decode all =
        AspisR1S9CurrentFieldOpsV1.decode first3 + AspisR1S9AfterScalarTermSumsV2.decW we3 ∧
      @AspisR1S9AfterScalarTermSumsV1.afterSums
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        ap1 side iterNext weights0 low first2 first3 all q4 q16 = .ok flow := by
  obtain ⟨q, q2, q4, q8, q12, q16, q1, low, high,
      hq, hkp, hq2, hq4, hq8, hq12, hq16, hscalar, htail,
      hhighArray, hhighCan, hhighDecode, hq16Can, hq16Decode⟩ :=
    AspisR1S9HighPowerPrefixSemanticsV1.active_body_high_powers
      ap0 ap1 extra side iterNext weights0
      flow hactive hextra
  have hseed : AspisR1S9HighPowerPrefixSemanticsV1.CanonicalQ q :=
    hextra side q hq
  have hlowCan :=
    AspisR1S9ConcreteScalarCallSemanticsV1.concrete_scalar_factor_low_canonical
      ap0 q1 low q hp0 hseed hkp hscalar
  have hscalarMeaning :=
    AspisR1S9ConcreteScalarCallSemanticsV1.concrete_scalar_factor_s2_meaning
      ap0 q1 low q hseed hkp hscalar hp0
  have hap1 : ∀ (j : U) (x : field.WideExact),
      Array.index_usize ap1 j = .ok x →
      AspisR1S9HighTermsTraceV1.canonicalW x := by
    intro j x hj
    change AspisR1CurrentWide.Proof.CanonicalWide
      (AspisR1S9GeneratedWideMulQM31V2.toWide x)
    rw [← AspisR1S9HighTermsConcreteV1.toE_eq_generated_toWide x]
    exact hp1 j x hj
  have hhigh : ∀ (j : U) (x : Q), Array.index_usize high j = .ok x →
      AspisR1S9HighTermsTraceV1.canonicalQ x := by
    intro j x hj
    change AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1S9GeneratedWideMulQM31V2.toQM x)
    have hmap : AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM x =
        AspisR1S9GeneratedWideMulQM31V2.toQM x := by
      cases x <;> rfl
    rw [← hmap]
    exact hhighCan j x hj
  obtain ⟨hterms⟩ := AspisR1S9HighTermsTraceV1.high_terms4_from_fn_p6
    ap1 high hap1 hhigh
  obtain ⟨terms, state, we, we1, first2, we2, first3, we3, all,
      hfromfn, hwe, hwe1, hadd2, hwe2, hadd3, hwe3, haddAll,
      hfirst2Can, hfirst2Dec, hfirst3Can, hfirst3Dec, hallCan, hallDec,
      hsums⟩ :=
    AspisR1S9AfterScalarTermSumsV2.after_scalar_success_terms_and_sums_mean
      ap0 ap1 extra side iterNext weights0 q4 q8 q12 q16 low
      flow htail high hhighArray hterms
  exact ⟨q, q1, q2, q4, q8, q12, q16, low, high, terms, state, hterms,
    we, we1, first2, we2, first3, we3, all,
    hq, hkp, hq2, hq4, hq8, hq12, hq16, hscalar, hscalarMeaning, hlowCan,
    htail, hhighArray, hhighCan, hhighDecode, hq16Can, hq16Decode,
    hfromfn, hwe, hwe1, hadd2, hwe2, hadd3, hwe3, haddAll,
    hfirst2Can, hfirst2Dec, hfirst3Can, hfirst3Dec, hallCan, hallDec, hsums⟩

#print axioms active_body_prefix_rich

end AspisR1S9BodyPrefixSemanticsV1
