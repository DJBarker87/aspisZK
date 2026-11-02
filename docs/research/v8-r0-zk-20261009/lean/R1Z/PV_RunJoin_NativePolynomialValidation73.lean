import R1Z.PV_RunJoin_NativePolynomialWindows73
import R1Z.PV_RunJoin_NativePolynomialBytes72
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativePolynomialValidation73
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
abbrev Q := aspis_core.field.QM31

theorem payload {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) (p : Nat → Q) (bytes : Slice U8)
    (value : bytes.val=PV_RunJoin_PolyLoop38.payload p 0 28) (row : U8) :
    @host_wire.validate_record_fields (types base) (opsNative base heap box ops runtime world)
      row bytes=ok (.Ok ()) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  have hlen : bytes.length=896 := by
    change bytes.val.length=896
    rw [value,PV_RunJoin_PolyLoop38.payload_length]
  exact PV_RunJoin_FieldValidation73.complete row bytes 28#usize 0#usize 28
    (PV_RunJoin_PolyOffsets73.divide bytes hlen) rfl (by decide)
    (by intro w e;rfl)
    (PV_RunJoin_NativePolynomialWindows73.complete base heap box ops runtime world p bytes value)

theorem complete {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) (values : Array Q 28#usize) :
    ∃ bytes, @host_sumcheck.encode_polynomial (types base) (opsNative base heap box ops runtime world)
      values=ok bytes ∧ bytes.length=896 ∧ ∀ row,
      @host_wire.validate_record_fields (types base) (opsNative base heap box ops runtime world)
        row (alloc.vec.Vec.deref bytes)=ok (.Ok ()) := by
  obtain ⟨bytes,hb,hv,hl⟩ := PV_RunJoin_NativePolynomialBytes72.complete base heap box ops runtime world values
  exact ⟨bytes,hb,hl,fun row => payload base heap box ops runtime world
    (PV_RunJoin_InterpolationInput72.cells values) (alloc.vec.Vec.deref bytes) hv row⟩

#print axioms payload
#print axioms complete
end R1Z.PV_RunJoin_NativePolynomialValidation73
