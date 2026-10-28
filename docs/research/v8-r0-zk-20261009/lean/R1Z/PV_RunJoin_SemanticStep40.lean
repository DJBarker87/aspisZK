import R1Z.PV_RunJoin_SemanticDomain40
set_option autoImplicit false
namespace R1Z.PV_RunJoin_SemanticStep40
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]

theorem next (logical : Slice U8) (count : U8) (out mid : alloc.vec.Vec U8)
    (at1 at2 : Usize) (row : U8) (more : row<count)
    (source : host_compact.compact_semantic_row logical out row at1=.ok (.Ok at2,mid)) :
    host_compact.compact_semantic_loop.body logical count out at1 row=
      .ok (.cont (mid,at2,U8.wrapping_add row 1#u8)) := by
  simp only [host_compact.compact_semantic_loop.body,more,↓reduceIte,
    source,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,lift]
  rfl

theorem stop (logical : Slice U8) (count row : U8) (out : alloc.vec.Vec U8)
    (at1 : Usize) (last : count≤row) (cursor : at1=Slice.len logical) :
    host_compact.compact_semantic_loop.body logical count out at1 row=
      .ok (.done (.Ok (),out)) := by
  simp only [host_compact.compact_semantic_loop.body,
    show ¬row<count from (by change ¬row.val<count.val;change count.val≤row.val at last;omega),
    ↓reduceIte,cursor,bne_self_eq_false,Bool.false_eq_true]

theorem trailing (logical : Slice U8) (count row : U8) (out : alloc.vec.Vec U8)
    (at1 : Usize) (last : count≤row) (cursor : at1≠Slice.len logical) :
    host_compact.compact_semantic_loop.body logical count out at1 row=
      .ok (.done (.Err compact.CodecError.Length,out)) := by
  simp only [host_compact.compact_semantic_loop.body,
    show ¬row<count from (by change ¬row.val<count.val;change count.val≤row.val at last;omega),
    ↓reduceIte,show (at1 != Slice.len logical)=true from (by simp only [bne_iff_ne];exact cursor)]
#print axioms next
#print axioms stop
#print axioms trailing
end R1Z.PV_RunJoin_SemanticStep40
