import R1Z.PV_RunJoin_RecordParser73
import R1Z.PV_RunJoin_FrameViews73
import R1Z.PV_RunJoin_NativePolynomialValidation73
import R1Z.PV_RunJoin_LayoutArithmetic41
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeRecordParse73
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
abbrev Q := aspis_core.field.QM31

theorem complete {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) (p : Nat → Q) (payload framed : Slice U8)
    (row tag : U8)
    (shape : @r1_wire.row_shape (types base) (opsNative base heap box ops runtime world) row=
      ok (some (tag,896#usize)))
    (value : payload.val=PV_RunJoin_PolyLoop38.payload p 0 28)
    (frame : framed.val=tag::(core.num.U32.to_le_bytes 896#u32).val++payload.val) :
    @host_wire.parse_record (types base) (opsNative base heap box ops runtime world)
      row framed=ok (.Ok payload) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  have valid := PV_RunJoin_NativePolynomialValidation73.payload base heap box ops runtime world p payload value row
  have length : Slice.len framed=901#usize := by
    apply UScalar.eq_of_val_eq
    change framed.val.length=(901#usize).val
    rw [frame,List.length_append,List.length_cons,(core.num.U32.to_le_bytes 896#u32).property,
      value,PV_RunJoin_PolyLoop38.payload_length]
    simp only [UScalar.ofNatCore_val_eq]
  have option : core.option.Option.ok_or (some (tag,896#usize)) r1_wire.Error.InvalidRow=
      ok (.Ok (tag,896#usize)) := rfl
  have cast : UScalar.cast .Usize 896#u32=896#usize := by scalar_tac
  have add := PV_RunJoin_LayoutArithmetic41.add 5#usize 896#usize 901#usize rfl
  rw [PV_RunJoin_RecordParser73.source]
  unfold PV_RunJoin_RecordParser73.parse
  simp only [shape,option,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
    Aeneas.Std.uncurry,lift,length,add,bne_self_eq_false,Bool.false_eq_true,if_false,
    PV_RunJoin_FrameViews73.tag framed payload tag 896#u32 frame,
    PV_RunJoin_FrameViews73.word framed payload tag 896#u32 frame,cast,
    PV_RunJoin_FrameViews73.payload framed payload tag 896#u32 frame,valid]
  split <;> rfl

#print axioms complete
end R1Z.PV_RunJoin_NativeRecordParse73
