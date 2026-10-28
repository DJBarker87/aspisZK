import R1Z.PV_RunJoin_ResultPost41
import R1Z.PV_RunJoin_ByteAppend38
import R1Z.PV_RunJoin_RowShapes41
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RecordFrame41
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultPost41
variable [ExternalTypes]

/-- Source framing independently of validation success: any successful return
is the exact constructed five-byte header and original payload. The parser's
failed/divergent Results are retained; no successful parser call is assumed. -/
theorem frame (ops : ExternalFuns) (row tag : U8) (size : Usize) (payload : Slice U8)
    (shape : @r1_wire.row_shape _ (ProverRwP6BodyCandidate.selected ops) row=
      .ok (some (tag,size))) (length : payload.length=size.val)
    (room : 5+size.val≤Usize.max) :
    ∃ header framed, header.length=5 ∧ framed.val=header ++ payload.val ∧
      Post (fun r : core.result.Result (alloc.vec.Vec U8) r1_wire.Error =>
        match r with | .Ok value => value=framed | .Err _ => True)
        (@host_wire.record _ (ProverRwP6BodyCandidate.selected ops) row payload) := by
  letI : ExternalFuns := ProverRwP6BodyCandidate.selected ops
  let out := alloc.vec.Vec.with_capacity U8 (Usize.wrapping_add 5#usize size)
  obtain ⟨one,h1,v1⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out tag (by
    change 0<Usize.max;scalar_tac))
  have l1 : one.length=1 := by
    change one.val.length=1
    rw [v1,List.length_append]
    rfl
  let word := core.num.U32.to_le_bytes (UScalar.cast .U32 size)
  have lw : (Array.to_slice word).length=4 := by
    simpa only [show (4#usize).val=4 from rfl] using word.property
  obtain ⟨head,hh,vh⟩ := PV_RunJoin_ByteAppend38.append one (Array.to_slice word) (by
    rw [lw,l1];omega)
  have lh : head.length=5 := by
    change head.val.length=5
    rw [vh,List.length_append]
    change one.length+(Array.to_slice word).length=5
    rw [lw,l1]
  obtain ⟨framed,hf,vf⟩ := PV_RunJoin_ByteAppend38.append head payload (by rw [lh,length];exact room)
  refine ⟨head.val,framed,lh,vf,?_⟩
  have lenword : Slice.len payload=size := by
    apply UScalar.eq_of_val_eq
    exact length
  have ho : core.option.Option.ok_or (some (tag,size)) r1_wire.Error.InvalidRow=
      .ok (.Ok (tag,size)) := rfl
  simp only [host_wire.record,shape,ho,core.result.Result.Insts.CoreOpsTry.branch,
    bind_tc_ok,lenword,bne_self_eq_false,Bool.false_eq_true,↓reduceIte,lift,h1,hh,hf]
  split
  · trivial
  · simp only [h1,hh,hf,bind_tc_ok]
    apply PV_RunJoin_ResultPost41.bind
    intro result
    cases result with
    | Ok value => rfl
    | Err error => trivial
#print axioms frame
end R1Z.PV_RunJoin_RecordFrame41
