import S9ActualTwoBodyCompositionV1
import S9BodyPrefixScalarVectorV1
import S9BodyPrefixPolynomialSumsV1
import S9OutputDecoderRemainingV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9ActualTwoBodyCoefficientsV17

open AspisR1S9HelperP6

abbrev W := AspisR1S9OutputDecoderLeafOneV5.W
abbrev Q := field.QM31
abbrev E := AspisR1S9OutputDecoderLeafOneV5.E
abbrev ExactQM := AspisR1CurrentWide.Proof.ExactQM
abbrev TraceDecode := AspisR1S9OutputDecoderLeafOneV5.TraceDecode
abbrev CurrentDecode := AspisR1S9BodyPrefixPolynomialSumsV1.CurrentDecode
abbrev Base := AspisR1S9BodyPrefixPolynomialSumsV1.Base
abbrev ScaledBase := AspisR1S9BodyPrefixPolynomialSumsV1.ScaledBase
abbrev Seed := AspisR1S9OutputDecoderLeafOneV5.Seed
abbrev cells := AspisR1S9OutputDecoderLeafOneV5.cells

private theorem current_decode_eq_trace_decode (x : field.WideExact) :
    CurrentDecode x = TraceDecode x := by
  change AspisR1CurrentWide.Proof.decodeWide
      (AspisR1S9CurrentFieldOpsV1.toE x) =
    AspisR1CurrentWide.Proof.decodeWide
      (AspisR1S9GeneratedWideMulQM31V2.toWide x)
  rw [AspisR1S9HighTermsConcreteV1.toE_eq_generated_toWide]

private theorem trace_decode_q_eq_high_decode_q (q : Q) :
    AspisR1S9BodyPrefixPolynomialSumsV1.TraceDecodeQ q =
      AspisR1S9HighPowerPrefixSemanticsV1.decodeQ q := by
  cases q <;> rfl

private theorem scalar_seed_eq (q : Q) :
    AspisR1S9BodyPrefixScalarVectorV1.Seed q = Seed q := by
  cases q <;> rfl

private theorem high_map_eq_seed (q : Q) :
    algebraMap ExactQM E (AspisR1S9HighPowerPrefixSemanticsV1.decodeQ q) = Seed q := by
  change algebraMap ExactQM E
      (AspisR1S9HighPowerPrefixSemanticsV1.decodeQ q) =
    algebraMap ExactQM E
      (AspisR1S9BodyPrefixPolynomialSumsV1.TraceDecodeQ q)
  rw [trace_decode_q_eq_high_decode_q]

private theorem generated_seed_eq_zero (q : Q) :
    algebraMap ExactQM E (AspisR1.S9SideZeroTailRootV1.qdecode q) = Seed q := by
  cases q <;> rfl

private theorem accepted_q_map_eq_seed (q : Q) :
    algebraMap ExactQM E
      (AspisR1.S9ConcreteArithmeticAcceptedRootV1.decodeQ q) = Seed q := by
  calc
    algebraMap ExactQM E
        (AspisR1.S9ConcreteArithmeticAcceptedRootV1.decodeQ q) =
      algebraMap ExactQM E
        (AspisR1S9HighPowerPrefixSemanticsV1.decodeQ q) :=
          congrArg (algebraMap ExactQM E)
            (AspisR1S9BodyPrefixPolynomialSumsV1.accepted_decodeQ_eq_high_power_decodeQ q)
    _ = Seed q := high_map_eq_seed q

private theorem q16_power
    (ap0 ap1 : W) (extra : Array Q (2#usize)) (side : Std.Usize)
    (iter : core.ops.range.Range Std.Usize) (weights : W)
    (flow : ControlFlow (core.ops.range.Range Std.Usize × W) W)
    (p : AspisR1S9BodyPrefixSemanticsV1.BodyPrefixWitness ap0 ap1 extra side iter weights flow) :
    Seed p.q16 = (Seed p.q)^16 := by
  have hq' : AspisR1S9HighPowerPrefixSemanticsV1.decodeQ p.q16 =
      AspisR1S9HighPowerPrefixSemanticsV1.decodeQ p.q ^ 16 := p.q16Decode
  calc
    Seed p.q16 = algebraMap ExactQM E
        (AspisR1S9HighPowerPrefixSemanticsV1.decodeQ p.q16) :=
          (high_map_eq_seed p.q16).symm
    _ = algebraMap ExactQM E
        (AspisR1S9HighPowerPrefixSemanticsV1.decodeQ p.q ^ 16) := congrArg _ hq'
    _ = (Seed p.q)^16 := by
          rw [map_pow, high_map_eq_seed]

private theorem q4_power
    (ap0 ap1 : W) (extra : Array Q (2#usize)) (side : Std.Usize)
    (iter : core.ops.range.Range Std.Usize) (weights : W)
    (flow : ControlFlow (core.ops.range.Range Usize × W) W)
    (p : AspisR1S9BodyPrefixSemanticsV1.BodyPrefixWitness ap0 ap1 extra side iter weights flow) :
    Seed p.q4 = (Seed p.q)^4 := by
  have hread : Array.index_usize p.high 1#usize = .ok p.q4 := by
    rw [p.highArray]
    rfl
  have hq := p.highDecode 1#usize p.q4 hread
  have hpow : 4 * (1#usize).val = 4 := by decide
  rw [hpow] at hq
  calc
    Seed p.q4 = algebraMap ExactQM E
        (AspisR1S9HighPowerPrefixSemanticsV1.decodeQ p.q4) :=
          (high_map_eq_seed p.q4).symm
    _ = algebraMap ExactQM E
        (AspisR1S9HighPowerPrefixSemanticsV1.decodeQ p.q ^ 4) := congrArg _ hq
    _ = (Seed p.q)^4 := by
          rw [map_pow, high_map_eq_seed]

private theorem last_cell
    (ap0 ap1 : W) (extra : Array Q (2#usize))
    (iter : core.ops.range.Range Std.Usize) (weights0 output : W)
    (one : AspisR1S9BodyOneRecordConsumerV1.BodyOneOutputWitness
      ap0 ap1 extra iter weights0 output) :
    one.last = cells ap1 (AspisR1.S2LibraFactoredIdentity.perm 3) := by
  have hidx : one.permIndex = 1#usize := Result.ok.inj
    (one.permRead.symm.trans AspisR1S9TransparentFoldS2InstanceV1.perm_reads.2.2.2)
  have hread := one.ap1Read
  rw [hidx] at hread
  have hcell := AspisR1.S9HighTermPolynomialMeaningRootV1.source_read_cell
    ap1 1#usize one.last (by decide) hread
  simpa [AspisR1.S9HighTermPolynomialMeaningRootV1.cell,
    AspisR1.S2LibraFactoredIdentity.perm] using hcell.symm

/-- The two actual selected-model active-body results compute the four S2
factored output coefficients for the same source arrays and challenges. -/
theorem two_body_output_factored
    (ap0 ap1 : W) (extra : Array Q (2#usize)) (initial middle output : W)
    (iter1 iter2 : core.ops.range.Range Std.Usize)
    (w : AspisR1S9ActualTwoBodyCompositionV1.TwoBodyOutputWitness
      ap0 ap1 extra iter1 iter2 initial middle output) :
    ∀ j : Fin 4,
      TraceDecode (cells output j) =
        AspisR1.S2LibraFactoredIdentity.factored
          (ScaledBase ap0) (ScaledBase ap1)
          (Seed w.sideZero.execution.q) (Seed w.sideOne.prefixData.q) j := by
  let z := w.sideZero.execution
  let o := w.sideOne.prefixData
  have hscalar0 := AspisR1S9BodyPrefixScalarVectorV1.scalar_factor_vector_meaning
    ap0 z.q1 z.low z.q z.scalarMeaning
  have hscalar1 := AspisR1S9BodyPrefixScalarVectorV1.scalar_factor_vector_meaning
    ap0 o.q1 o.low o.q o.scalarMeaning
  have hscalar0' : TraceDecode z.low =
      AspisR1.S2LibraFactoredIdentity.scalar (ScaledBase ap0) (Seed z.q) := by
    simpa only [scalar_seed_eq] using hscalar0
  have hscalar1' : TraceDecode o.low =
      AspisR1.S2LibraFactoredIdentity.scalar (ScaledBase ap0) (Seed o.q) := by
    simpa only [scalar_seed_eq] using hscalar1
  have hsum0 := AspisR1S9BodyPrefixPolynomialSumsV1.body_prefix_sums_match_source_polynomials
    ap0 ap1 extra 0#usize iter1 initial (.cont (iter1, middle)) z
  have hsum1 := AspisR1S9BodyPrefixPolynomialSumsV1.body_prefix_sums_match_source_polynomials
    ap0 ap1 extra 1#usize iter2 middle (.cont (iter2, output)) o
  have hfirst3z : TraceDecode z.first3 =
      AspisR1.S2LibraFactoredIdentity.firstThree (ScaledBase ap1) (Seed z.q) := by
    calc
      TraceDecode z.first3 = CurrentDecode z.first3 :=
        (current_decode_eq_trace_decode z.first3).symm
      _ = _ := hsum0.2.1
  have hallz : TraceDecode z.all =
      AspisR1.S2LibraFactoredIdentity.allFour (ScaledBase ap1) (Seed z.q) := by
    calc
      TraceDecode z.all = CurrentDecode z.all :=
        (current_decode_eq_trace_decode z.all).symm
      _ = _ := hsum0.2.2
  have hfirst2o : TraceDecode o.first2 =
      AspisR1.S2LibraFactoredIdentity.firstTwo (ScaledBase ap1) (Seed o.q) := by
    calc
      TraceDecode o.first2 = CurrentDecode o.first2 :=
        (current_decode_eq_trace_decode o.first2).symm
      _ = _ := hsum1.1
  have hallo : TraceDecode o.all =
      AspisR1.S2LibraFactoredIdentity.allFour (ScaledBase ap1) (Seed o.q) := by
    calc
      TraceDecode o.all = CurrentDecode o.all :=
        (current_decode_eq_trace_decode o.all).symm
      _ = _ := hsum1.2.2
  have hq16z := q16_power ap0 ap1 extra 0#usize iter1 initial (.cont (iter1, middle)) z
  have hq4o := q4_power ap0 ap1 extra 1#usize iter2 middle (.cont (iter2, output)) o
  have hq16o := q16_power ap0 ap1 extra 1#usize iter2 middle (.cont (iter2, output)) o
  have hlast : TraceDecode w.sideOne.last =
      Base ap1 (AspisR1.S2LibraFactoredIdentity.perm 3) := by
    have hcell := last_cell ap0 ap1 extra iter2 middle output w.sideOne
    change TraceDecode w.sideOne.last = _
    rw [hcell]
  have hframe : cells output ⟨0, by decide⟩ = cells middle ⟨0, by decide⟩ := by
    exact AspisR1.S9SideOneFrameRootV1.sideOneTail_preserves_cell_zero
      middle ap1 output o.low o.all o.first2 o.q4 o.q16
      (AspisR1S9BodyOneRecordConsumerV1.side_one_source_tail_success
        ap0 ap1 extra iter2 middle output o)
  have hz0 : TraceDecode (cells output ⟨0, by decide⟩) =
      TraceDecode z.low * TraceDecode z.all := by
    rw [hframe]
    exact AspisR1S9OutputDecoderRemainingV3.zero_middle_cell0
      ap0 ap1 extra iter1 initial middle w.sideZero
  have hz1raw := AspisR1S9OutputDecoderLeafOneV5.zero_middle_cell1
    ap0 ap1 extra iter1 initial middle w.sideZero
  have hz1 : TraceDecode (cells middle ⟨1, by decide⟩) =
      (TraceDecode z.low * TraceDecode z.first3) * (Seed z.q)^16 := by
    dsimp only [z, TraceDecode, Seed, cells, E, W,
      AspisR1S9OutputDecoderLeafOneV5.TraceDecode,
      AspisR1S9OutputDecoderLeafOneV5.Seed,
      AspisR1S9OutputDecoderLeafOneV5.E,
      AspisR1S9OutputDecoderLeafOneV5.W,
      AspisR1S9OutputDecoderLeafOneV5.cells,
      AspisR1S9OutputDecoderRemainingV3.TraceDecode,
      AspisR1S9OutputDecoderRemainingV3.Seed,
      AspisR1S9OutputDecoderRemainingV3.E,
      AspisR1S9OutputDecoderRemainingV3.W,
      AspisR1S9OutputDecoderRemainingV3.cells,
      AspisR1S9BodyPrefixPolynomialSumsV1.TraceDecode,
      AspisR1S9BodyPrefixPolynomialSumsV1.Seed,
      AspisR1S9BodyPrefixPolynomialSumsV1.TraceDecodeQ,
      AspisR1S9BodyPrefixPolynomialSumsV1.E,
      AspisR1S9BodyPrefixSemanticsV1.W, AspisR1S9BodyPrefixSemanticsV1.U,
      AspisR1S9CurrentFieldOpsV1.S] at hz1raw ⊢
    exact hz1raw
  have ho1 : TraceDecode (cells output ⟨1, by decide⟩) =
      TraceDecode (cells middle ⟨1, by decide⟩) +
        TraceDecode o.low * (TraceDecode w.sideOne.last *
          AspisR1S9BodyPrefixPolynomialSumsV1.Quarter) :=
    AspisR1S9OutputDecoderRemainingV3.one_output_cell1
      ap0 ap1 extra iter2 middle output w.sideOne
  have ho2raw := AspisR1S9OutputDecoderRemainingV3.one_output_cell2
    ap0 ap1 extra iter2 middle output w.sideOne
  have ho2 : TraceDecode (cells output ⟨2, by decide⟩) =
      (TraceDecode o.low * TraceDecode o.all) * (Seed o.q)^4 := by
    dsimp only [o, TraceDecode, Seed, cells, E, W,
      AspisR1S9OutputDecoderRemainingV3.TraceDecode,
      AspisR1S9OutputDecoderRemainingV3.Seed,
      AspisR1S9OutputDecoderRemainingV3.E,
      AspisR1S9OutputDecoderRemainingV3.W,
      AspisR1S9OutputDecoderRemainingV3.cells,
      AspisR1S9OutputDecoderLeafOneV5.TraceDecode,
      AspisR1S9OutputDecoderLeafOneV5.Seed,
      AspisR1S9OutputDecoderLeafOneV5.E,
      AspisR1S9OutputDecoderLeafOneV5.W,
      AspisR1S9OutputDecoderLeafOneV5.cells,
      AspisR1S9BodyPrefixPolynomialSumsV1.TraceDecode,
      AspisR1S9BodyPrefixPolynomialSumsV1.Seed,
      AspisR1S9BodyPrefixPolynomialSumsV1.TraceDecodeQ,
      AspisR1S9BodyPrefixPolynomialSumsV1.E,
      AspisR1S9BodyPrefixSemanticsV1.W, AspisR1S9BodyPrefixSemanticsV1.U,
      AspisR1S9CurrentFieldOpsV1.S] at ho2raw ⊢
    exact ho2raw
  have ho3raw := AspisR1S9OutputDecoderRemainingV3.one_output_cell3
    ap0 ap1 extra iter2 middle output w.sideOne
  have ho3 : TraceDecode (cells output ⟨3, by decide⟩) =
      (TraceDecode o.low * TraceDecode o.first2) * ((Seed o.q)^16 * (Seed o.q)^4) := by
    dsimp only [o, TraceDecode, Seed, cells, E, W,
      AspisR1S9OutputDecoderRemainingV3.TraceDecode,
      AspisR1S9OutputDecoderRemainingV3.Seed,
      AspisR1S9OutputDecoderRemainingV3.E,
      AspisR1S9OutputDecoderRemainingV3.W,
      AspisR1S9OutputDecoderRemainingV3.cells,
      AspisR1S9OutputDecoderLeafOneV5.TraceDecode,
      AspisR1S9OutputDecoderLeafOneV5.Seed,
      AspisR1S9OutputDecoderLeafOneV5.E,
      AspisR1S9OutputDecoderLeafOneV5.W,
      AspisR1S9OutputDecoderLeafOneV5.cells,
      AspisR1S9BodyPrefixPolynomialSumsV1.TraceDecode,
      AspisR1S9BodyPrefixPolynomialSumsV1.Seed,
      AspisR1S9BodyPrefixPolynomialSumsV1.TraceDecodeQ,
      AspisR1S9BodyPrefixPolynomialSumsV1.E,
      AspisR1S9BodyPrefixSemanticsV1.W, AspisR1S9BodyPrefixSemanticsV1.U,
      AspisR1S9CurrentFieldOpsV1.S] at ho3raw ⊢
    exact ho3raw
  intro j
  fin_cases j
  · rw [AspisR1.S2LibraFactoredIdentity.factored]
    simp only [Fin.val_mk, if_pos (show (0 : Nat) = 0 by decide), if_true, if_false]
    rw [hz0, hscalar0', hallz]
  · rw [AspisR1.S2LibraFactoredIdentity.factored]
    simp only [Fin.val_mk, if_neg (show (1 : Nat) ≠ 0 by decide), if_pos (show (1 : Nat) = 1 by decide), if_true, if_false]
    rw [ho1, hz1, hscalar0', hfirst3z, hscalar1', hlast]
    simp only [AspisR1.S2LibraFactoredIdentity.scaled]
    ring
  · rw [AspisR1.S2LibraFactoredIdentity.factored]
    simp only [Fin.val_mk, if_neg (show (2 : Nat) ≠ 0 by decide), if_neg (show (2 : Nat) ≠ 1 by decide), if_pos (show (2 : Nat) = 2 by decide), if_true, if_false]
    rw [ho2, hscalar1', hallo]
  · rw [AspisR1.S2LibraFactoredIdentity.factored]
    simp only [Fin.val_mk, if_neg (show (3 : Nat) ≠ 0 by decide), if_neg (show (3 : Nat) ≠ 1 by decide), if_neg (show (3 : Nat) ≠ 2 by decide), if_true, if_false]
    rw [ho3, hscalar1', hfirst2o]
    rw [← pow_add, show (16 : Nat) + 4 = 20 by decide]

#print axioms two_body_output_factored

end AspisR1S9ActualTwoBodyCoefficientsV17
