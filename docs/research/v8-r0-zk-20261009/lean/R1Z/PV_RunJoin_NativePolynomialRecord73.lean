import R1Z.PV_RunJoin_NativeRecordParse73
import R1Z.PV_RunJoin_ByteAppend38
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativePolynomialRecord73
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
abbrev Q := aspis_core.field.QM31

theorem capacity : (901 : Nat) ≤ Usize.max := by scalar_tac
#print axioms capacity

theorem complete {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) (p : Nat → Q) (payload : Slice U8)
    (row tag : U8)
    (shape : @r1_wire.row_shape (types base) (opsNative base heap box ops runtime world) row=
      ok (some (tag,896#usize)))
    (value : payload.val=PV_RunJoin_PolyLoop38.payload p 0 28) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box ops runtime world
    ∃ framed, host_wire.record row payload=ok (.Ok framed) ∧
      framed.val=tag::(core.num.U32.to_le_bytes 896#u32).val++payload.val ∧
      framed.length=901 ∧ host_wire.parse_record row (alloc.vec.Vec.deref framed)=ok (.Ok payload) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  have len : payload.length=896 := by
    change payload.val.length=896
    rw [value,PV_RunJoin_PolyLoop38.payload_length]
  have size : Slice.len payload=896#usize := UScalar.eq_of_val_eq len
  have add := PV_RunJoin_LayoutArithmetic41.add 5#usize 896#usize 901#usize rfl
  have cast : UScalar.cast .U32 896#usize=896#u32 := by scalar_tac
  let out := alloc.vec.Vec.with_capacity U8 901#usize
  obtain ⟨one,h1,v1⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out tag (by
    change 0<Usize.max;scalar_tac))
  have oneval : one.val=[tag] := by rw [v1];rfl
  have oneLen : one.length=1 := by change one.val.length=1;rw [oneval];rfl
  let word := core.num.U32.to_le_bytes 896#u32
  have wordLen : (Array.to_slice word).length=4 := by
    rw [Array.length_to_slice];rfl
  obtain ⟨head,hh,vh⟩ := PV_RunJoin_ByteAppend38.append one (Array.to_slice word) (by
    rw [oneLen,wordLen];have cap := capacity;omega)
  have headLen : head.length=5 := by
    change head.val.length=5
    rw [vh,List.length_append]
    change one.length+(Array.to_slice word).length=5
    rw [oneLen,wordLen]
  obtain ⟨framed,hf,vf⟩ := PV_RunJoin_ByteAppend38.append head payload (by
    rw [headLen,len];exact capacity)
  have frame : framed.val=tag::word.val++payload.val := by
    rw [vf,vh,oneval]
    rfl
  have total : framed.length=901 := by
    change framed.val.length=901
    rw [frame,List.length_append,List.length_cons,word.property]
    change 1+4+payload.length=901
    rw [len]
  have parsed := PV_RunJoin_NativeRecordParse73.complete base heap box ops runtime world
    p payload (alloc.vec.Vec.deref framed) row tag shape value frame
  have option : core.option.Option.ok_or (some (tag,896#usize)) r1_wire.Error.InvalidRow=
      ok (.Ok (tag,896#usize)) := rfl
  refine ⟨framed,?_,frame,total,parsed⟩
  dsimp only [out,word] at h1 hh
  simp only [host_wire.record,shape,option,core.result.Result.Insts.CoreOpsTry.branch,
    bind_tc_ok,Aeneas.Std.uncurry,size,bne_self_eq_false,Bool.false_eq_true,if_false,lift,
    add,h1,cast,hh,hf,parsed]

#print axioms complete
end R1Z.PV_RunJoin_NativePolynomialRecord73
