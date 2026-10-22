import S9OutputDecoderLeafOneV1
import S9OutputDecoderRemainingV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9OutputConversionDiagnosticV1

open AspisR1S9HelperP6

abbrev W := AspisR1S9OutputDecoderLeafOneV5.W
abbrev Q := field.QM31
abbrev E := AspisR1S9OutputDecoderLeafOneV5.E
abbrev TraceDecode := AspisR1S9OutputDecoderLeafOneV5.TraceDecode
abbrev Seed := AspisR1S9OutputDecoderLeafOneV5.Seed
abbrev cells := AspisR1S9OutputDecoderLeafOneV5.cells

private theorem current_decode_eq_trace_decode (x : field.WideExact) :
    AspisR1S9BodyPrefixPolynomialSumsV1.CurrentDecode x = TraceDecode x := by
  change AspisR1CurrentWide.Proof.decodeWide
      (AspisR1S9CurrentFieldOpsV1.toE x) =
    AspisR1CurrentWide.Proof.decodeWide
      (AspisR1S9GeneratedWideMulQM31V2.toWide x)
  rw [AspisR1S9HighTermsConcreteV1.toE_eq_generated_toWide]

private theorem zero_map_eq_seed (q : Q) :
    algebraMap AspisR1S9HelperP6PowerSemanticsV1.ExactQM E
      (AspisR1.S9SideZeroTailRootV1.qdecode q) = Seed q := by
  cases q <;> rfl

 theorem diag_zero
    (ap0 ap1 : W) (extra : Array Q (2#usize))
    (iter : core.ops.range.Range Std.Usize) (weights0 middle : W)
    (z : AspisR1S9BodyPrefixSemanticsV1.BodyZeroOutputWitness
      ap0 ap1 extra iter weights0 middle) :
    TraceDecode (cells middle ⟨1, by decide⟩) =
      (TraceDecode z.execution.low * TraceDecode z.execution.first3) *
        (Seed z.execution.q)^16 := by
  have hzraw := AspisR1S9OutputDecoderLeafOneV5.zero_middle_cell1
    ap0 ap1 extra iter weights0 middle z
  dsimp only [TraceDecode, Seed, cells, E, W,
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
    AspisR1S9BodyPrefixSemanticsV1.W,
    AspisR1S9BodyPrefixSemanticsV1.U,
    AspisR1S9CurrentFieldOpsV1.S] at hzraw ⊢
  exact hzraw

 theorem diag_one_two
    (ap0 ap1 : W) (extra : Array Q (2#usize))
    (iter : core.ops.range.Range Std.Usize) (weights0 output : W)
    (o : AspisR1S9BodyOneRecordConsumerV1.BodyOneOutputWitness
      ap0 ap1 extra iter weights0 output) :
    TraceDecode (cells output ⟨2, by decide⟩) =
      (TraceDecode o.prefixData.low * TraceDecode o.prefixData.all) *
        (Seed o.prefixData.q)^4 := by
  have horaw := AspisR1S9OutputDecoderRemainingV3.one_output_cell2
    ap0 ap1 extra iter weights0 output o
  dsimp only [TraceDecode, Seed, cells, E, W,
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
    AspisR1S9BodyPrefixSemanticsV1.W,
    AspisR1S9BodyPrefixSemanticsV1.U,
    AspisR1S9CurrentFieldOpsV1.S] at horaw ⊢
  exact horaw

#print axioms diag_zero
#print axioms diag_one_two

end AspisR1S9OutputConversionDiagnosticV1
