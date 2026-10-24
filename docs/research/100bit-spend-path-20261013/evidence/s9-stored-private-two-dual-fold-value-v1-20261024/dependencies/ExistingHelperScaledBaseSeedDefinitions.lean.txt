import S9BodyPrefixWitnessV1
import S9HighTermPolynomialMeaningRootV2

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9BodyPrefixPolynomialSumsV1

open AspisR1S9HelperP6
open AspisR1S9BodyPrefixSemanticsV1

abbrev W := field.WideExact
abbrev Q := field.QM31
abbrev CurrentDecode := AspisR1S9CurrentFieldOpsV1.decode
abbrev TraceDecode := AspisR1S9HighTermsTraceV1.decW
abbrev TraceDecodeQ := AspisR1S9HighTermsTraceV1.decQ
abbrev Quarter := AspisR1CurrentWide.Proof.wideScalarEmbedding weights.QUARTER
abbrev E := AspisWideTower.WideExact
abbrev Base (ap1 : Array W (4#usize)) : Fin 4 → E :=
  fun j => TraceDecode (AspisR1.S9ArrayWriteScheduleRootV1.cells ap1 j)
abbrev ScaledBase (ap1 : Array W (4#usize)) : Fin 4 → E :=
  AspisR1.S2LibraFactoredIdentity.scaled (Base ap1) Quarter
abbrev Seed (q : Q) : E :=
  algebraMap AspisR1S9HelperP6PowerSemanticsV1.ExactQM E (TraceDecodeQ q)

private theorem current_decode_eq_trace_decode (x : W) :
    CurrentDecode x = TraceDecode x := by
  change AspisR1CurrentWide.Proof.decodeWide
    (AspisR1S9CurrentFieldOpsV1.toE x) =
    AspisR1CurrentWide.Proof.decodeWide
      (AspisR1S9GeneratedWideMulQM31V2.toWide x)
  rw [AspisR1S9HighTermsConcreteV1.toE_eq_generated_toWide]

private theorem trace_decode_q_eq_high_decode_q (x : Q) :
    TraceDecodeQ x = AspisR1S9HighPowerPrefixSemanticsV1.decodeQ x := by
  cases x <;> rfl

/-- The accepted-arithmetic and high-power source decoders are the same
carrier map on the shared QM31 values. -/
theorem accepted_decodeQ_eq_high_power_decodeQ (x : Q) :
    AspisR1.S9ConcreteArithmeticAcceptedRootV1.decodeQ x =
      AspisR1S9HighPowerPrefixSemanticsV1.decodeQ x := by
  cases x <;> rfl

/-- The selected from_fn result in the body record is the same returned array
as the four-call HighTerms witness. Its four recorded sums therefore have the
source polynomial meanings for the same ap1 and seed. -/
theorem body_prefix_sums_match_source_polynomials
    (ap0 ap1 : Array W (4#usize)) (extra : Array Q (2#usize))
    (side : Std.Usize) (iterNext : core.ops.range.Range Std.Usize)
    (weights0 : Array W (4#usize))
    (flow : ControlFlow (core.ops.range.Range Std.Usize × Array W (4#usize))
      (Array W (4#usize)))
    (pfx : BodyPrefixWitness ap0 ap1 extra side iterNext weights0 flow) :
    CurrentDecode pfx.first2 =
        AspisR1.S2LibraFactoredIdentity.firstTwo (ScaledBase ap1) (Seed pfx.q) ∧
    CurrentDecode pfx.first3 =
        AspisR1.S2LibraFactoredIdentity.firstThree (ScaledBase ap1) (Seed pfx.q) ∧
    CurrentDecode pfx.all =
        AspisR1.S2LibraFactoredIdentity.allFour (ScaledBase ap1) (Seed pfx.q) := by
  have htermsPair := Result.ok.inj (pfx.fromFn.symm.trans pfx.hterms.generated_from_fn)
  have htermsEq : pfx.terms = pfx.hterms.terms := congrArg Prod.fst htermsPair
  have hread0 : Array.index_usize pfx.hterms.terms 0#usize = .ok pfx.hterms.call0.term := by
    unfold Array.index_usize
    rw [Array.getElem?_Usize_eq]
    rw [pfx.hterms.terms_values]
    rfl
  have hread1 : Array.index_usize pfx.hterms.terms 1#usize = .ok pfx.hterms.call1.term := by
    unfold Array.index_usize
    rw [Array.getElem?_Usize_eq]
    rw [pfx.hterms.terms_values]
    rfl
  have hread2 : Array.index_usize pfx.hterms.terms 2#usize = .ok pfx.hterms.call2.term := by
    unfold Array.index_usize
    rw [Array.getElem?_Usize_eq]
    rw [pfx.hterms.terms_values]
    rfl
  have hread3 : Array.index_usize pfx.hterms.terms 3#usize = .ok pfx.hterms.call3.term := by
    unfold Array.index_usize
    rw [Array.getElem?_Usize_eq]
    rw [pfx.hterms.terms_values]
    rfl
  have hbody0 : Array.index_usize pfx.hterms.terms 0#usize = .ok pfx.we := by
    rw [← htermsEq]
    exact pfx.readWe
  have hbody1 : Array.index_usize pfx.hterms.terms 1#usize = .ok pfx.we1 := by
    rw [← htermsEq]
    exact pfx.readWe1
  have hbody2 : Array.index_usize pfx.hterms.terms 2#usize = .ok pfx.we2 := by
    rw [← htermsEq]
    exact pfx.readWe2
  have hbody3 : Array.index_usize pfx.hterms.terms 3#usize = .ok pfx.we3 := by
    rw [← htermsEq]
    exact pfx.readWe3
  have hwe0 : pfx.we = pfx.hterms.call0.term := Result.ok.inj (hbody0.symm.trans hread0)
  have hwe1 : pfx.we1 = pfx.hterms.call1.term := Result.ok.inj (hbody1.symm.trans hread1)
  have hwe2 : pfx.we2 = pfx.hterms.call2.term := Result.ok.inj (hbody2.symm.trans hread2)
  have hwe3 : pfx.we3 = pfx.hterms.call3.term := Result.ok.inj (hbody3.symm.trans hread3)
  have hhigh : ∀ j z, Array.index_usize pfx.high j = .ok z →
      TraceDecodeQ z = TraceDecodeQ pfx.q ^ (4*j.val) := by
    intro j z hj
    rw [trace_decode_q_eq_high_decode_q z, trace_decode_q_eq_high_decode_q pfx.q]
    exact pfx.highDecode j z hj
  have ht0 := AspisR1.S9HighTermPolynomialMeaningRootV1.actual_term_is_scaled_power
    ap1 pfx.high pfx.q 0#usize (by decide) pfx.hterms.call0 hhigh
  dsimp only [AspisR1.S9HighTermPolynomialMeaningRootV1.D,
    AspisR1.S9HighTermPolynomialMeaningRootV1.DQ] at ht0
  have ht1 := AspisR1.S9HighTermPolynomialMeaningRootV1.actual_term_is_scaled_power
    ap1 pfx.high pfx.q 1#usize (by decide) pfx.hterms.call1 hhigh
  dsimp only [AspisR1.S9HighTermPolynomialMeaningRootV1.D,
    AspisR1.S9HighTermPolynomialMeaningRootV1.DQ] at ht1
  have ht2 := AspisR1.S9HighTermPolynomialMeaningRootV1.actual_term_is_scaled_power
    ap1 pfx.high pfx.q 2#usize (by decide) pfx.hterms.call2 hhigh
  dsimp only [AspisR1.S9HighTermPolynomialMeaningRootV1.D,
    AspisR1.S9HighTermPolynomialMeaningRootV1.DQ] at ht2
  have ht3 := AspisR1.S9HighTermPolynomialMeaningRootV1.actual_term_is_scaled_power
    ap1 pfx.high pfx.q 3#usize (by decide) pfx.hterms.call3 hhigh
  dsimp only [AspisR1.S9HighTermPolynomialMeaningRootV1.D,
    AspisR1.S9HighTermPolynomialMeaningRootV1.DQ] at ht3
  have hsum2Current : CurrentDecode pfx.first2 = CurrentDecode pfx.we + CurrentDecode pfx.we1 := by
    change AspisR1S9CurrentFieldOpsV1.decode pfx.first2 =
      AspisR1S9AfterScalarTermSumsV2.decW pfx.we +
        AspisR1S9AfterScalarTermSumsV2.decW pfx.we1
    exact pfx.first2Decode
  have hsum3Current : CurrentDecode pfx.first3 = CurrentDecode pfx.first2 + CurrentDecode pfx.we2 := by
    change AspisR1S9CurrentFieldOpsV1.decode pfx.first3 =
      AspisR1S9CurrentFieldOpsV1.decode pfx.first2 +
        AspisR1S9AfterScalarTermSumsV2.decW pfx.we2
    exact pfx.first3Decode
  have hsum4Current : CurrentDecode pfx.all = CurrentDecode pfx.first3 + CurrentDecode pfx.we3 := by
    change AspisR1S9CurrentFieldOpsV1.decode pfx.all =
      AspisR1S9CurrentFieldOpsV1.decode pfx.first3 +
        AspisR1S9AfterScalarTermSumsV2.decW pfx.we3
    exact pfx.allDecode
  have hsum2 : TraceDecode pfx.first2 = TraceDecode pfx.we + TraceDecode pfx.we1 := by
    calc
      TraceDecode pfx.first2 = CurrentDecode pfx.first2 :=
        (current_decode_eq_trace_decode pfx.first2).symm
      _ = CurrentDecode pfx.we + CurrentDecode pfx.we1 := hsum2Current
      _ = TraceDecode pfx.we + TraceDecode pfx.we1 := by
        rw [current_decode_eq_trace_decode pfx.we,
          current_decode_eq_trace_decode pfx.we1]
  have hsum3 : TraceDecode pfx.first3 = TraceDecode pfx.first2 + TraceDecode pfx.we2 := by
    calc
      TraceDecode pfx.first3 = CurrentDecode pfx.first3 :=
        (current_decode_eq_trace_decode pfx.first3).symm
      _ = CurrentDecode pfx.first2 + CurrentDecode pfx.we2 := hsum3Current
      _ = TraceDecode pfx.first2 + TraceDecode pfx.we2 := by
        rw [current_decode_eq_trace_decode pfx.first2,
          current_decode_eq_trace_decode pfx.we2]
  have hsum4 : TraceDecode pfx.all = TraceDecode pfx.first3 + TraceDecode pfx.we3 := by
    calc
      TraceDecode pfx.all = CurrentDecode pfx.all :=
        (current_decode_eq_trace_decode pfx.all).symm
      _ = CurrentDecode pfx.first3 + CurrentDecode pfx.we3 := hsum4Current
      _ = TraceDecode pfx.first3 + TraceDecode pfx.we3 := by
        rw [current_decode_eq_trace_decode pfx.first3,
          current_decode_eq_trace_decode pfx.we3]
  dsimp only [TraceDecode, TraceDecodeQ] at ht0 ht1 ht2 ht3 hsum2 hsum3 hsum4
  constructor
  · rw [current_decode_eq_trace_decode pfx.first2]
    dsimp only [TraceDecode, TraceDecodeQ]
    rw [hsum2, hwe0, ht0, hwe1, ht1]
    simp [AspisR1.S2LibraFactoredIdentity.firstTwo,
      AspisR1.S2LibraFactoredIdentity.scaled,
      AspisR1.S2LibraFactoredIdentity.perm, Base, Seed]
  constructor
  · rw [current_decode_eq_trace_decode pfx.first3]
    dsimp only [TraceDecode, TraceDecodeQ]
    rw [hsum3, hwe2, ht2]
    rw [hsum2, hwe0, ht0, hwe1, ht1]
    simp [AspisR1.S2LibraFactoredIdentity.firstThree,
      AspisR1.S2LibraFactoredIdentity.firstTwo,
      AspisR1.S2LibraFactoredIdentity.scaled,
      AspisR1.S2LibraFactoredIdentity.perm, Base, Seed]
  · rw [current_decode_eq_trace_decode pfx.all]
    dsimp only [TraceDecode, TraceDecodeQ]
    rw [hsum4, hwe3, ht3]
    rw [hsum3, hwe2, ht2]
    rw [hsum2, hwe0, ht0, hwe1, ht1]
    simp [AspisR1.S2LibraFactoredIdentity.allFour,
      AspisR1.S2LibraFactoredIdentity.firstThree,
      AspisR1.S2LibraFactoredIdentity.firstTwo,
      AspisR1.S2LibraFactoredIdentity.scaled,
      AspisR1.S2LibraFactoredIdentity.perm, Base, Seed]

#print axioms body_prefix_sums_match_source_polynomials

end AspisR1S9BodyPrefixPolynomialSumsV1
