import NGD_ParseReference
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGO_ParseDomain
open AspisR1PrefixAggregateParser
/-- Any reached successful parse has the exact header-imposed framed length,
independently of the full validator reply. This is an input-producer domain
fact, not a premise asserting decoder or validator correctness. -/
theorem header_size
    (validate : U8 → Slice U8 → Result (core.result.Result Unit r1_wire.Error))
    (row tag : U8) (size total : Usize) (record payload : Slice U8)
    (shape : r1_wire.row_shape row=ok (some (tag,size)))
    (addition : 5#usize+size=ok total)
    (run : NGD_ParseCut.invoke validate row record=ok (.Ok payload)) :
    record.val.length=5+size.val := by
  have spec := UScalar.add_equiv 5#usize size
  rw [addition] at spec
  have totalValue : total.val=5+size.val := by simpa using spec.2.1
  by_contra wrong
  have different : Slice.len record≠total := by
    intro equal
    have eq:=congrArg UScalar.val equal
    change record.val.length=total.val at eq
    omega
  simp only [NGD_ParseCut.invoke,shape,core.option.Option.ok_or,
    core.result.Result.Insts.CoreOpsTry.branch,addition,bind_tc_ok] at run
  simp [AspisR1PrefixAggregateParser.core.option.Option.ok_or,addition,totalValue,wrong] at run
#print axioms header_size
end NGO_ParseDomain
