import NDF_ParserDomain
set_option autoImplicit false
namespace NDF_AcceptedFrame
open Aeneas Aeneas.Std Result

theorem wrong_length (row tag : U8) (size total : Usize) (bs : Slice U8)
    (shape : AspisR1PrefixAggregateParser.r1_wire.row_shape row=ok (some (tag,size)))
    (sum : 5#usize+size=ok total) (different : Slice.len bs≠total) :
    AspisR1PrefixAggregateParser.r1_wire.parse_record row bs=ok (.Err (.Length row)) := by
  simp_all [AspisR1PrefixAggregateParser.r1_wire.parse_record,
    AspisR1PrefixAggregateParser.core.option.Option.ok_or,
    core.result.Result.Insts.CoreOpsTry.branch]

theorem accepted (row tag : U8) (size : Usize) (bs payload : Slice U8)
    (shape : AspisR1PrefixAggregateParser.r1_wire.row_shape row=ok (some (tag,size)))
    (success : AspisR1PrefixAggregateParser.r1_wire.parse_record row bs=ok (.Ok payload)) :
    bs.val.length≤3717 := by
  have cap := (NDF_ParserDomain.shape_bound row tag size shape).1
  obtain ⟨total,add,value⟩ := WP.spec_imp_exists (Usize.add_spec (x:=5#usize) (y:=size) (by scalar_tac))
  have length : Slice.len bs=total := by
    by_contra different
    have reject := wrong_length row tag size total bs shape add different
    rw [reject] at success
    cases success
  have same : bs.val.length=total.val := congrArg UScalar.val length
  have five : (5#usize).val=5 := by scalar_tac
  rw [five] at value
  omega

#print axioms wrong_length
#print axioms accepted
end NDF_AcceptedFrame
