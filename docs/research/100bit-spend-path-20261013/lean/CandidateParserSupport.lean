import R1CandidateFieldParsers
import R1M31ParserArray

/-! Small support lemmas for the retained candidate field parser.  The Option
    try/residual plumbing follows the already-used R260 proof route. -/
set_option autoImplicit false

namespace AspisR1.CandidateParserSupport

open Aeneas Aeneas.Std Result

theorem branch_none (T : Type) :
    AspisR1CandidateParser.core.option.Option.Insts.CoreOpsTry_traitTry.branch
      (none : Option T) =
        .ok (Aeneas.Std.core.ops.control_flow.ControlFlow.Break none) := rfl

theorem branch_some {T : Type} (x : T) :
    AspisR1CandidateParser.core.option.Option.Insts.CoreOpsTry_traitTry.branch
      (some x) =
        .ok (Aeneas.Std.core.ops.control_flow.ControlFlow.Continue x) := rfl

private theorem residual_none (T : Type) :
    AspisR1CandidateParser.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
      T none = .ok none := by
  simp [AspisR1CandidateParser.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
    massert, read_discriminant, AspisR1CandidateParser.optionDiscriminant,
    AspisR1CandidateParser.optionTag, bind_tc_ok]

theorem residual_complete (T : Type)
    (o : Option Aeneas.Std.core.convert.Infallible) :
    AspisR1CandidateParser.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
      T o = .ok none := by
  cases o with
  | none => exact residual_none T
  | some x => cases x

theorem m31_from_le_bytes_eq_extracted (arr : Array U8 4#usize) :
    AspisR1CandidateParser.field.M31.from_le_bytes arr =
      AspisR1M31Parser.field.M31.from_le_bytes arr := by
  simp [AspisR1CandidateParser.field.M31.from_le_bytes,
    AspisR1M31Parser.field.M31.from_le_bytes,
    AspisR1CandidateParser.field.P, AspisR1M31Parser.field.P]

theorem parser_refines_array (arr : Array U8 4#usize) :
    AspisR1CandidateParser.field.M31.from_le_bytes arr =
      Result.ok ((AspisR1.RetainedFieldByteCodec.decodeM31LE
        (AspisR1.M31ParserArray.arrayBytes arr)).map
          AspisR1.M31ParserRefinement.valueToU32) := by
  rw [m31_from_le_bytes_eq_extracted arr]
  exact AspisR1.M31ParserArray.parser_refines_array arr

#print axioms branch_none
#print axioms branch_some
#print axioms residual_complete
#print axioms m31_from_le_bytes_eq_extracted
#print axioms parser_refines_array

end AspisR1.CandidateParserSupport
