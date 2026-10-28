import R1Z.PV_RunJoin_ByteSlice40
import R1Z.PV_RunJoin_CompactStep39
import R1Z.ProverRwP6BodyCandidate
set_option autoImplicit false
namespace R1Z.PV_RunJoin_SemanticCopy40
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] (ops : ExternalFuns)
local instance : ExternalFuns := ProverRwP6BodyCandidate.selected ops

/-- A message-free or uncompressed semantic row retains its five-byte header
and exact payload. The source row-shape law is supplied separately. -/
theorem row (logical : Slice U8) (out : alloc.vec.Vec U8) (row tag : U8)
    (at1 size : Usize) (shape : r1_wire.row_shape row=.ok (some (tag,size)))
    (small : row.val<14) (bound : at1.val+5+size.val≤logical.length)
    (room : out.length+5+size.val≤Usize.max) :
    ∃ next, host_compact.compact_semantic_row logical out row at1=
      .ok (.Ok (Usize.wrapping_add (Usize.wrapping_add at1 5#usize) size),next) ∧
      next.val=out.val ++ (logical.val.drop at1.val).take 5 ++
        (logical.val.drop (at1.val+5)).take size.val := by
  have cap : logical.length≤Usize.max := logical.property
  have inc : (Usize.wrapping_add at1 5#usize).val=at1.val+5 :=
    PV_RunJoin_CompactStep39.offset at1 5#usize (by change at1.val+5≤Usize.max;omega)
  have endval : (Usize.wrapping_add (Usize.wrapping_add at1 5#usize) size).val=
      at1.val+5+size.val := by
    rw [PV_RunJoin_CompactStep39.offset _ size (by rw [inc];omega),inc]
  obtain ⟨head,mid,hh,hm,hmid⟩ := PV_RunJoin_ByteRange39.append logical out at1
    (Usize.wrapping_add at1 5#usize) (by rw [inc];omega) (by rw [inc];omega)
    (by rw [inc];omega)
  have midlen : mid.length=out.length+5 := by
    change mid.val.length=out.val.length+5
    rw [hmid,List.length_append,List.length_take,List.length_drop,inc]
    have hl : logical.length=logical.val.length := rfl
    rw [hl] at bound
    omega
  obtain ⟨payload,next,hp,hn,hnext⟩ := PV_RunJoin_ByteRange39.append logical mid
    (Usize.wrapping_add at1 5#usize)
    (Usize.wrapping_add (Usize.wrapping_add at1 5#usize) size)
    (by rw [inc,endval];omega) (by rw [endval];exact bound)
    (by rw [endval,inc,midlen];omega)
  have ho : core.option.Option.ok_or (some (tag,size)) compact.CodecError.Length=
      .ok (.Ok (tag,size)) := rfl
  refine ⟨next,?_,?_⟩
  · simp only [host_compact.compact_semantic_row,shape,
      ho,core.result.Result.Insts.CoreOpsTry.branch,
      bind_tc_ok,lift,hh,hm,host_compact.compact_row,
      show ¬row≥14#u8 from (by change ¬row.val≥14;omega),Bool.decide_false,↓reduceIte,hp,hn]
  · rw [hnext,hmid,inc,endval]
    simp only [Nat.add_sub_cancel_left]
#print axioms row
end R1Z.PV_RunJoin_SemanticCopy40
