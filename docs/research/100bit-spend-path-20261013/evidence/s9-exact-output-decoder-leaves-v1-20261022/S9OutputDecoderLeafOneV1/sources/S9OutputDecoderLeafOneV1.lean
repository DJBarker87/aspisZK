import S9BodyZeroConsumerV1
import S9BodyOneRecordConsumerV1
import S9BodyPrefixPolynomialSumsV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9OutputDecoderLeafOneV5

open AspisR1S9HelperP6

abbrev W := AspisR1S9BodyPrefixSemanticsV1.W
abbrev Q := field.QM31
abbrev E := AspisWideTower.WideExact
abbrev ExactQM := AspisR1CurrentWide.Proof.ExactQM
abbrev TraceDecode := AspisR1S9BodyPrefixPolynomialSumsV1.TraceDecode
abbrev CurrentDecode := AspisR1S9BodyPrefixPolynomialSumsV1.CurrentDecode
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
  change algebraMap ExactQM E
      (AspisR1S9HighPowerPrefixSemanticsV1.decodeQ q) =
    algebraMap ExactQM E
      (AspisR1S9BodyPrefixPolynomialSumsV1.TraceDecodeQ q)
  rw [trace_decode_q_eq_high_decode_q]

private theorem zero_map_eq_seed (q : Q) :
    algebraMap ExactQM E (AspisR1.S9SideZeroTailRootV1.qdecode q) = Seed q := by
  cases q <;> rfl

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
        (AspisR1S9HighPowerPrefixSemanticsV1.decodeQ p.q16) :=
          (high_map_eq_seed p.q16).symm
    _ = algebraMap ExactQM E
        (AspisR1S9HighPowerPrefixSemanticsV1.decodeQ p.q ^ 16) := congrArg _ hq
    _ = (Seed p.q)^16 := by
          rw [map_pow]
          exact congrArg (fun x => x ^ 16) (high_map_eq_seed p.q)

private theorem select_one (j : Fin 4) (a b c : E)
    (h0 : j.val ≠ 0) (h1 : j.val = 1) :
    (if j.val = 0 then a else if j.val = 1 then b else c) = b := by
  simp [h0, h1]

theorem zero_middle_cell1
    (ap0 ap1 : W) (extra : Array Q (2#usize))
    (iter : core.ops.range.Range Std.Usize) (weights0 middle : W)
    (z : AspisR1S9BodyPrefixSemanticsV1.BodyZeroOutputWitness
      ap0 ap1 extra iter weights0 middle) :
    TraceDecode (cells middle ⟨1, by decide⟩) =
      (TraceDecode z.execution.low * TraceDecode z.execution.first3) *
        (Seed z.execution.q)^16 := by
  let j : Fin 4 := ⟨1, by decide⟩
  have h0 : j.val ≠ 0 := by decide
  have h1 : j.val = 1 := rfl
  have hz0 := z.outputMeaning j
  have hselect := select_one j
    (AspisR1.S9SideZeroTailRootV1.decode z.execution.low *
      AspisR1.S9SideZeroTailRootV1.decode z.execution.all)
    ((AspisR1.S9SideZeroTailRootV1.decode z.execution.low *
      AspisR1.S9SideZeroTailRootV1.decode z.execution.first3) *
      algebraMap AspisR1S9HelperP6PowerSemanticsV1.ExactQM E
        (AspisR1.S9SideZeroTailRootV1.qdecode z.execution.q16))
    (AspisR1.S9SideZeroTailRootV1.decode
      (cells weights0 j)) h0 h1
  have hz := hz0.trans hselect
  dsimp only [AspisR1.S9SideZeroTailRootV1.decode] at hz
  simp only [current_decode_eq_trace_decode] at hz
  rw [zero_map_eq_seed,
    q16_power ap0 ap1 extra 0#usize iter weights0 (.cont (iter, middle)) z.execution] at hz
  dsimp only [j, E, W,
    AspisR1S9BodyPrefixPolynomialSumsV1.E,
    AspisR1S9BodyPrefixSemanticsV1.W,
    AspisR1S9BodyPrefixSemanticsV1.U,
    AspisR1S9CurrentFieldOpsV1.S] at hz ⊢
  exact hz

#print axioms zero_middle_cell1

end AspisR1S9OutputDecoderLeafOneV5
