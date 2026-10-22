import S9OutputDecoderLeafOneV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9OutputDecoderRemainingV3

open AspisR1S9HelperP6

abbrev W := AspisR1S9BodyPrefixSemanticsV1.W
abbrev Q := field.QM31
abbrev E := AspisWideTower.WideExact
abbrev ExactQM := AspisR1CurrentWide.Proof.ExactQM
abbrev TraceDecode := AspisR1S9BodyPrefixPolynomialSumsV1.TraceDecode
abbrev Seed := AspisR1S9BodyPrefixPolynomialSumsV1.Seed
abbrev Quarter := AspisR1S9BodyPrefixPolynomialSumsV1.Quarter
abbrev cells (a : W) (j : Fin 4) := AspisR1.S9ArrayWriteScheduleRootV1.cells a j

private theorem current_decode_eq_trace_decode (x : field.WideExact) :
    AspisR1S9CurrentFieldOpsV1.decode x = TraceDecode x := by
  change AspisR1CurrentWide.Proof.decodeWide
      (AspisR1S9CurrentFieldOpsV1.toE x) =
    AspisR1CurrentWide.Proof.decodeWide
      (AspisR1S9GeneratedWideMulQM31V2.toWide x)
  rw [AspisR1S9HighTermsConcreteV1.toE_eq_generated_toWide]

private theorem trace_decode_q_eq_high_decode_q (q : Q) :
    AspisR1S9BodyPrefixPolynomialSumsV1.TraceDecodeQ q =
      AspisR1S9HighPowerPrefixSemanticsV1.decodeQ q := by
  cases q <;> rfl

private theorem high_map_eq_seed (q : Q) :
    algebraMap ExactQM E (AspisR1S9HighPowerPrefixSemanticsV1.decodeQ q) = Seed q := by
  change algebraMap ExactQM E (AspisR1S9HighPowerPrefixSemanticsV1.decodeQ q) =
    algebraMap ExactQM E (AspisR1S9BodyPrefixPolynomialSumsV1.TraceDecodeQ q)
  rw [trace_decode_q_eq_high_decode_q]

private theorem zero_map_eq_seed (q : Q) :
    algebraMap ExactQM E (AspisR1.S9SideZeroTailRootV1.qdecode q) = Seed q := by
  cases q <;> rfl

private theorem accepted_map_eq_seed (q : Q) :
    algebraMap ExactQM E
      (AspisR1.S9ConcreteArithmeticAcceptedRootV1.decodeQ q) = Seed q := by
  calc
    algebraMap ExactQM E (AspisR1.S9ConcreteArithmeticAcceptedRootV1.decodeQ q) =
      algebraMap ExactQM E (AspisR1S9HighPowerPrefixSemanticsV1.decodeQ q) :=
        congrArg (algebraMap ExactQM E)
          (AspisR1S9BodyPrefixPolynomialSumsV1.accepted_decodeQ_eq_high_power_decodeQ q)
    _ = Seed q := high_map_eq_seed q

private theorem q16_power
    (ap0 ap1 : W) (extra : Array Q (2#usize)) (side : Std.Usize)
    (iter : core.ops.range.Range Std.Usize) (weights : W)
    (flow : ControlFlow (core.ops.range.Range Std.Usize × W) W)
    (p : AspisR1S9BodyPrefixSemanticsV1.BodyPrefixWitness ap0 ap1 extra side iter weights flow) :
    Seed p.q16 = (Seed p.q)^16 := by
  have hq : AspisR1S9HighPowerPrefixSemanticsV1.decodeQ p.q16 =
      AspisR1S9HighPowerPrefixSemanticsV1.decodeQ p.q ^ 16 := p.q16Decode
  calc
    Seed p.q16 = algebraMap ExactQM E
      (AspisR1S9HighPowerPrefixSemanticsV1.decodeQ p.q16) := (high_map_eq_seed p.q16).symm
    _ = algebraMap ExactQM E
      (AspisR1S9HighPowerPrefixSemanticsV1.decodeQ p.q ^ 16) := congrArg _ hq
    _ = (Seed p.q)^16 := by rw [map_pow]; exact congrArg (fun x => x^16) (high_map_eq_seed p.q)

private theorem q4_power
    (ap0 ap1 : W) (extra : Array Q (2#usize)) (side : Std.Usize)
    (iter : core.ops.range.Range Std.Usize) (weights : W)
    (flow : ControlFlow (core.ops.range.Range Usize × W) W)
    (p : AspisR1S9BodyPrefixSemanticsV1.BodyPrefixWitness ap0 ap1 extra side iter weights flow) :
    Seed p.q4 = (Seed p.q)^4 := by
  have hread : Array.index_usize p.high 1#usize = .ok p.q4 := by rw [p.highArray]; rfl
  have hq := p.highDecode 1#usize p.q4 hread
  have hpow : 4 * (1#usize).val = 4 := by decide
  rw [hpow] at hq
  calc
    Seed p.q4 = algebraMap ExactQM E
      (AspisR1S9HighPowerPrefixSemanticsV1.decodeQ p.q4) := (high_map_eq_seed p.q4).symm
    _ = algebraMap ExactQM E
      (AspisR1S9HighPowerPrefixSemanticsV1.decodeQ p.q ^ 4) := congrArg _ hq
    _ = (Seed p.q)^4 := by rw [map_pow]; exact congrArg (fun x => x^4) (high_map_eq_seed p.q)

private theorem select_zero (j : Fin 4) (a b c : E)
    (h0 : j.val = 0) :
    (if j.val = 0 then a else if j.val = 1 then b else c) = a := by
  simp [h0]

private theorem select_one (j : Fin 4) (a b c : E)
    (h0 : j.val ≠ 0) (h1 : j.val = 1) :
    (if j.val = 0 then a else if j.val = 1 then b else c) = b := by
  simp [h0, h1]

private theorem select_one4 (j : Fin 4) (a b c d : E)
    (h0 : j.val ≠ 0) (h1 : j.val = 1) :
    (if j.val = 0 then a else if j.val = 1 then b else if j.val = 2 then c else d) = b := by
  simp [h0, h1]

private theorem select_two (j : Fin 4) (a b c d : E)
    (h0 : j.val ≠ 0) (h1 : j.val ≠ 1) (h2 : j.val = 2) :
    (if j.val = 0 then a else if j.val = 1 then b else if j.val = 2 then c else d) = c := by
  simp [h0, h1, h2]

private theorem select_three (j : Fin 4) (a b c d : E)
    (h0 : j.val ≠ 0) (h1 : j.val ≠ 1) (h2 : j.val ≠ 2) :
    (if j.val = 0 then a else if j.val = 1 then b else if j.val = 2 then c else d) = d := by
  simp [h0, h1, h2]

theorem zero_middle_cell0
    (ap0 ap1 : W) (extra : Array Q (2#usize))
    (iter : core.ops.range.Range Std.Usize) (weights0 middle : W)
    (z : AspisR1S9BodyPrefixSemanticsV1.BodyZeroOutputWitness ap0 ap1 extra iter weights0 middle) :
    TraceDecode (cells middle ⟨0, by decide⟩) =
      TraceDecode z.execution.low * TraceDecode z.execution.all := by
  let j : Fin 4 := ⟨0, by decide⟩
  have h0 : j.val = 0 := rfl
  have hz0 := z.outputMeaning j
  have hsel := select_zero j
    (AspisR1.S9SideZeroTailRootV1.decode z.execution.low * AspisR1.S9SideZeroTailRootV1.decode z.execution.all)
    ((AspisR1.S9SideZeroTailRootV1.decode z.execution.low * AspisR1.S9SideZeroTailRootV1.decode z.execution.first3) *
      algebraMap ExactQM E (AspisR1.S9SideZeroTailRootV1.qdecode z.execution.q16))
    (AspisR1.S9SideZeroTailRootV1.decode (cells weights0 j)) h0
  have hz := hz0.trans hsel
  dsimp only [AspisR1.S9SideZeroTailRootV1.decode] at hz
  simp only [current_decode_eq_trace_decode] at hz
  dsimp only [j, E, W, AspisR1S9BodyPrefixPolynomialSumsV1.E,
    AspisR1S9BodyPrefixSemanticsV1.W, AspisR1S9BodyPrefixSemanticsV1.U,
    AspisR1S9CurrentFieldOpsV1.S] at hz ⊢
  exact hz

theorem one_output_cell1
    (ap0 ap1 : W) (extra : Array Q (2#usize))
    (iter : core.ops.range.Range Std.Usize) (weights0 output : W)
    (o : AspisR1S9BodyOneRecordConsumerV1.BodyOneOutputWitness ap0 ap1 extra iter weights0 output) :
    TraceDecode (cells output ⟨1, by decide⟩) =
      TraceDecode (cells weights0 ⟨1, by decide⟩) +
        TraceDecode o.prefixData.low * (TraceDecode o.last * Quarter) := by
  let j : Fin 4 := ⟨1, by decide⟩
  have h0 : j.val ≠ 0 := by decide
  have h1 : j.val = 1 := rfl
  have ho0 := o.outputMeaning j
  have hsel := select_one4 j
    (AspisR1S9CurrentFieldOpsV1.decode (cells weights0 j))
    (AspisR1S9CurrentFieldOpsV1.decode (cells weights0 1) +
      AspisR1S9CurrentFieldOpsV1.decode o.prefixData.low *
        (AspisR1S9CurrentFieldOpsV1.decode o.last *
          AspisR1CurrentWide.Proof.wideScalarEmbedding AspisR1S9HelperP6.weights.QUARTER))
    ((AspisR1S9CurrentFieldOpsV1.decode o.prefixData.low * AspisR1S9CurrentFieldOpsV1.decode o.prefixData.all) *
      algebraMap ExactQM E (AspisR1.S9ConcreteArithmeticAcceptedRootV1.decodeQ o.prefixData.q4))
    ((AspisR1S9CurrentFieldOpsV1.decode o.prefixData.low * AspisR1S9CurrentFieldOpsV1.decode o.prefixData.first2) *
      (algebraMap ExactQM E (AspisR1.S9ConcreteArithmeticAcceptedRootV1.decodeQ o.prefixData.q16) *
        algebraMap ExactQM E (AspisR1.S9ConcreteArithmeticAcceptedRootV1.decodeQ o.prefixData.q4))) h0 h1
  have ho := ho0.trans hsel
  simp only [current_decode_eq_trace_decode] at ho
  dsimp only [j, E, W, AspisR1S9BodyPrefixPolynomialSumsV1.E,
    AspisR1S9BodyPrefixSemanticsV1.W, AspisR1S9BodyPrefixSemanticsV1.U,
    AspisR1S9CurrentFieldOpsV1.S] at ho ⊢
  exact ho

theorem one_output_cell2
    (ap0 ap1 : W) (extra : Array Q (2#usize))
    (iter : core.ops.range.Range Std.Usize) (weights0 output : W)
    (o : AspisR1S9BodyOneRecordConsumerV1.BodyOneOutputWitness ap0 ap1 extra iter weights0 output) :
    TraceDecode (cells output ⟨2, by decide⟩) =
      (TraceDecode o.prefixData.low * TraceDecode o.prefixData.all) *
        (Seed o.prefixData.q)^4 := by
  let j : Fin 4 := ⟨2, by decide⟩
  have h0 : j.val ≠ 0 := by decide
  have h1 : j.val ≠ 1 := by decide
  have h2 : j.val = 2 := rfl
  have ho0 := o.outputMeaning j
  have hsel := select_two j
    (AspisR1S9CurrentFieldOpsV1.decode (cells weights0 j))
    (AspisR1S9CurrentFieldOpsV1.decode (cells weights0 1) +
      AspisR1S9CurrentFieldOpsV1.decode o.prefixData.low *
        (AspisR1S9CurrentFieldOpsV1.decode o.last *
          AspisR1CurrentWide.Proof.wideScalarEmbedding AspisR1S9HelperP6.weights.QUARTER))
    ((AspisR1S9CurrentFieldOpsV1.decode o.prefixData.low * AspisR1S9CurrentFieldOpsV1.decode o.prefixData.all) *
      algebraMap ExactQM E (AspisR1.S9ConcreteArithmeticAcceptedRootV1.decodeQ o.prefixData.q4))
    ((AspisR1S9CurrentFieldOpsV1.decode o.prefixData.low * AspisR1S9CurrentFieldOpsV1.decode o.prefixData.first2) *
      (algebraMap ExactQM E (AspisR1.S9ConcreteArithmeticAcceptedRootV1.decodeQ o.prefixData.q16) *
        algebraMap ExactQM E (AspisR1.S9ConcreteArithmeticAcceptedRootV1.decodeQ o.prefixData.q4))) h0 h1 h2
  have ho := ho0.trans hsel
  simp only [current_decode_eq_trace_decode] at ho
  rw [accepted_map_eq_seed,
    q4_power ap0 ap1 extra 1#usize iter weights0 (.cont (iter, output)) o.prefixData] at ho
  dsimp only [j, E, W, AspisR1S9BodyPrefixPolynomialSumsV1.E,
    AspisR1S9BodyPrefixSemanticsV1.W, AspisR1S9BodyPrefixSemanticsV1.U,
    AspisR1S9CurrentFieldOpsV1.S] at ho ⊢
  exact ho

theorem one_output_cell3
    (ap0 ap1 : W) (extra : Array Q (2#usize))
    (iter : core.ops.range.Range Std.Usize) (weights0 output : W)
    (o : AspisR1S9BodyOneRecordConsumerV1.BodyOneOutputWitness ap0 ap1 extra iter weights0 output) :
    TraceDecode (cells output ⟨3, by decide⟩) =
      (TraceDecode o.prefixData.low * TraceDecode o.prefixData.first2) *
        ((Seed o.prefixData.q)^16 * (Seed o.prefixData.q)^4) := by
  let j : Fin 4 := ⟨3, by decide⟩
  have h0 : j.val ≠ 0 := by decide
  have h1 : j.val ≠ 1 := by decide
  have h2 : j.val ≠ 2 := by decide
  have ho0 := o.outputMeaning j
  have hsel := select_three j
    (AspisR1S9CurrentFieldOpsV1.decode (cells weights0 j))
    (AspisR1S9CurrentFieldOpsV1.decode (cells weights0 1) +
      AspisR1S9CurrentFieldOpsV1.decode o.prefixData.low *
        (AspisR1S9CurrentFieldOpsV1.decode o.last *
          AspisR1CurrentWide.Proof.wideScalarEmbedding AspisR1S9HelperP6.weights.QUARTER))
    ((AspisR1S9CurrentFieldOpsV1.decode o.prefixData.low * AspisR1S9CurrentFieldOpsV1.decode o.prefixData.all) *
      algebraMap ExactQM E (AspisR1.S9ConcreteArithmeticAcceptedRootV1.decodeQ o.prefixData.q4))
    ((AspisR1S9CurrentFieldOpsV1.decode o.prefixData.low * AspisR1S9CurrentFieldOpsV1.decode o.prefixData.first2) *
      (algebraMap ExactQM E (AspisR1.S9ConcreteArithmeticAcceptedRootV1.decodeQ o.prefixData.q16) *
        algebraMap ExactQM E (AspisR1.S9ConcreteArithmeticAcceptedRootV1.decodeQ o.prefixData.q4))) h0 h1 h2
  have ho := ho0.trans hsel
  simp only [current_decode_eq_trace_decode] at ho
  rw [accepted_map_eq_seed, accepted_map_eq_seed,
    q16_power ap0 ap1 extra 1#usize iter weights0 (.cont (iter, output)) o.prefixData,
    q4_power ap0 ap1 extra 1#usize iter weights0 (.cont (iter, output)) o.prefixData] at ho
  dsimp only [j, E, W, AspisR1S9BodyPrefixPolynomialSumsV1.E,
    AspisR1S9BodyPrefixSemanticsV1.W, AspisR1S9BodyPrefixSemanticsV1.U,
    AspisR1S9CurrentFieldOpsV1.S] at ho ⊢
  exact ho

#print axioms zero_middle_cell0
#print axioms one_output_cell1
#print axioms one_output_cell2
#print axioms one_output_cell3

end AspisR1S9OutputDecoderRemainingV3
