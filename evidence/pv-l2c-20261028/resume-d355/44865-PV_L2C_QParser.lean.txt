import PV_L2C_ComplexParser
import PV_L2C_ParserHalves8
set_option autoImplicit false
namespace PV_L2C_QParser
open Aeneas Aeneas.Std Result PV_CB_ShippedOp71

def complexBytes (x y : U32) : Array U8 8#usize :=
  ⟨(PV_L2C_ParserSlices.pair (core.num.U32.to_le_bytes x) (core.num.U32.to_le_bytes y)).val,by
    have hx := (core.num.U32.to_le_bytes x).property
    have hy := (core.num.U32.to_le_bytes y).property
    simp only [PV_L2C_ParserSlices.pair,List.length_append]
    omega⟩

theorem complex_parse (x y : U32) (hx : x.val<2147483647) (hy : y.val<2147483647) :
    aspis_core.field.CM31.from_le_bytes (PV_L2C_ParserSlices.slice (complexBytes x y))=
      ok (some ⟨x,y⟩) :=
  PV_L2C_ComplexParser.parse x y hx hy
#print axioms complex_parse

/-- Full extracted QM31 parser on four canonical native words. The two
complex parses and every Result/Option branch are retained. -/
theorem parse (a b c d : U32) (ha : a.val<2147483647) (hb : b.val<2147483647)
    (hc : c.val<2147483647) (hd : d.val<2147483647) :
    aspis_core.field.QM31.from_le_bytes
      (PV_L2C_ParserHalves8.pair (complexBytes a b) (complexBytes c d))=
      ok (some ⟨⟨a,b⟩,⟨c,d⟩⟩) := by
  unfold aspis_core.field.QM31.from_le_bytes
  simp only [core.slice.index.Slice.index]
  rw [PV_L2C_ParserHalves8.left]
  simp only [bind_tc_ok,complex_parse a b ha hb,
    core.option.Option.Insts.CoreOpsTry_traitTry.branch]
  rw [PV_L2C_ParserHalves8.right]
  simp only [bind_tc_ok,complex_parse c d hc hd]
  rfl
#print axioms parse
end PV_L2C_QParser
