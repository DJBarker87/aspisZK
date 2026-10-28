import R1Z.PV_RunJoin_SemanticCopy40
import R1Z.PV_RunJoin_HighDomain40
import R1Z.PV_RunJoin_CompactSize39
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SemanticCompact40
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]

def low (bytes : List U8) (n : Nat) : List U8 :=
  (List.ofFn (fun i : Fin n => (bytes.drop (32*i.val)).take 16)).flatten

/-- A complete compressed row: preserve its five header bytes, check all high
halves, and retain low halves in source order. No compactor success is assumed. -/
theorem row (ops : ExternalFuns) (logical : Slice U8) (out : alloc.vec.Vec U8)
    (row tag : U8) (at1 size : Usize) (n : Nat)
    (shape : @r1_wire.row_shape _ (ProverRwP6BodyCandidate.selected ops) row=.ok (some (tag,size)))
    (large : 14≤row.val) (sizeval : size.val=32*n)
    (bound : at1.val+5+size.val≤logical.length)
    (room : out.length+5+16*n≤Usize.max)
    (zero : PV_RunJoin_HighDomain40.HighZero
      ((logical.val.drop (at1.val+5)).take size.val)) :
    ∃ next, @host_compact.compact_semantic_row _ (ProverRwP6BodyCandidate.selected ops)
      logical out row at1=.ok (.Ok (Usize.wrapping_add (Usize.wrapping_add at1 5#usize) size),next) ∧
      next.val=out.val ++ (logical.val.drop at1.val).take 5 ++
        low ((logical.val.drop (at1.val+5)).take size.val) n ∧
      next.length=out.length+5+16*n := by
  letI : ExternalFuns := ProverRwP6BodyCandidate.selected ops
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
  obtain ⟨s,hs,hval,hlen⟩ := PV_RunJoin_ByteSlice40.range logical
    (Usize.wrapping_add at1 5#usize)
    (Usize.wrapping_add (Usize.wrapping_add at1 5#usize) size)
    (by rw [inc,endval];omega) (by rw [endval];exact bound)
  have hv : s.val=(logical.val.drop (at1.val+5)).take size.val := by
    simpa only [inc,endval,Nat.add_sub_cancel_left] using hval
  have slen : s.length=32*n := by rw [hlen,endval,inc];omega
  obtain ⟨next,hn,hnext,nextlen⟩ := PV_RunJoin_CompactSize39.encode s mid n slen
    (by rw [midlen];exact room)
    (PV_RunJoin_HighDomain40.reads s (by rw [hv];exact zero))
  have ho : core.option.Option.ok_or (some (tag,size)) compact.CodecError.Length=
      .ok (.Ok (tag,size)) := rfl
  refine ⟨next,?_,?_,by rw [nextlen,midlen]⟩
  · simp only [host_compact.compact_semantic_row,shape,ho,
      core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift,hh,hm,
      host_compact.compact_row,show row≥14#u8 from large,decide_true,↓reduceIte]
    change (do
      let s1 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        logical { start := (Usize.wrapping_add at1 5#usize), «end» := (Usize.wrapping_add (Usize.wrapping_add at1 5#usize) size) }
      let (r1,out2) ← host_compact.compact_values s1 mid
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | .Continue _ => Result.ok (core.result.Result.Ok (E := compact.CodecError)
          (Usize.wrapping_add (Usize.wrapping_add at1 5#usize) size),out2)
      | .Break residual => do
        let r2 ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Usize (core.convert.FromSame compact.CodecError) residual
        Result.ok (r2,out2)) = _
    rw [hs]
    simp only [bind_tc_ok,hn,core.result.Result.Insts.CoreOpsTry.branch]
  · rw [hnext,hmid,hv,inc]
    simp only [low,Nat.add_sub_cancel_left,List.append_assoc]
#print axioms row
end R1Z.PV_RunJoin_SemanticCompact40
