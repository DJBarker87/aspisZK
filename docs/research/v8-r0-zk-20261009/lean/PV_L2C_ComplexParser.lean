import PV_L2C_ParserSlices
set_option autoImplicit false
namespace PV_L2C_ComplexParser
open Aeneas Aeneas.Std Result PV_CB_ShippedOp71 PV_L2C_ParserSlices

/-- Actual extracted CM31 parser, including both copies and all Result layers. -/
theorem parse (x y : U32) (hx : x.val<2147483647) (hy : y.val<2147483647) :
    aspis_core.field.CM31.from_le_bytes
      (pair (core.num.U32.to_le_bytes x) (core.num.U32.to_le_bytes y))=
      ok (some ⟨x,y⟩) := by
  unfold aspis_core.field.CM31.from_le_bytes
  simp only [core.slice.index.Slice.index,core.slice.index.SliceIndexRangeUsizeSlice]
  rw [left]
  simp only [bind_tc_ok,copy_array]
  rw [PV_L2C_CanonicalParser.scalar_parse x hx]
  simp only [bind_tc_ok,core.option.Option.Insts.CoreOpsTry_traitTry.branch]
  rw [right]
  simp only [bind_tc_ok,copy_array]
  rw [PV_L2C_CanonicalParser.scalar_parse y hy]
  rfl
#print axioms parse
end PV_L2C_ComplexParser
