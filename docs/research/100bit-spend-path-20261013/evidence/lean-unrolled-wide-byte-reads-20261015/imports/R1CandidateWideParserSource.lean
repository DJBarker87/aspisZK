import R1CandidateFieldParsers

/-! Exact newly generated Wide parser declarations, relocated into the already
checked candidate parser namespace. All shared field and Option declarations
are byte-identical and reused by import; tools/retain-wide-parser.py checks
this partition against the full generated Types/Funs and LLBC metadata.
This isolated candidate is not yet the deployed/runtime Wide parser. -/
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false

namespace AspisR1CandidateParser

/-- [aspis_core::field::wide_exact::WideExact]
    Source: 'field/wide_exact.rs', lines 28:0-31:1
    Visibility: public -/
structure field.wide_exact.WideExact where
  c0 : field.QM31
  c1 : field.QM31

/-- [aspis_core::field::wide_exact::{aspis_core::field::wide_exact::WideExact}::BYTE_LEN]
    Source: 'field/wide_exact.rs', lines 35:4-35:35
    Visibility: public -/
@[global_simps, irreducible]
def field.wide_exact.WideExact.BYTE_LEN : Std.Usize := 32#usize

/-- [aspis_core::field::wide_exact::{aspis_core::field::wide_exact::WideExact}::from_le_bytes]:
    Source: 'field/wide_exact.rs', lines 254:4-261:5
    Visibility: public -/
def field.wide_exact.WideExact.from_le_bytes
  (bytes : Slice Std.U8) : Result (Option field.wide_exact.WideExact) := do
  let i := Slice.len bytes
  if i != field.wide_exact.WideExact.BYTE_LEN
  then ok none
  else
    let s ←
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) bytes { start := 0#usize, «end» := 16#usize }
    let o ← field.QM31.from_le_bytes s
    let cf ← core.option.Option.Insts.CoreOpsTry_traitTry.branch o
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let s1 ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
          { start := 16#usize, «end» := 32#usize }
      let o1 ← field.QM31.from_le_bytes s1
      let cf1 ← core.option.Option.Insts.CoreOpsTry_traitTry.branch o1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        ok (some { c0 := val, c1 := val1 })
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
          field.wide_exact.WideExact residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
        field.wide_exact.WideExact residual

/-- [aspis_core::parse_wide_exact_probe]:
    Source: 'lib.rs', lines 7:0-9:1
    Visibility: public -/
def parse_wide_exact_probe
  (bytes : Slice Std.U8) : Result (Option field.wide_exact.WideExact) := do
  field.wide_exact.WideExact.from_le_bytes bytes

end AspisR1CandidateParser

#print axioms AspisR1CandidateParser.field.wide_exact.WideExact
#print axioms AspisR1CandidateParser.field.wide_exact.WideExact.BYTE_LEN
#print axioms AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes
#print axioms AspisR1CandidateParser.parse_wide_exact_probe
