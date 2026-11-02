import R1Z.PV_RunJoin_NativeCanonicalParse73
import R1Z.PV_RunJoin_PolyPayloadCanonicalWindow73
import R1Z.PV_RunJoin_PolyOffsets73
import R1Z.PV_RunJoin_FieldValidation73
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativePolynomialWindows73
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
abbrev Q := aspis_core.field.QM31

theorem complete {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) (p : Nat → Q) (bytes : Slice U8)
    (value : bytes.val=@PV_RunJoin_PolyLoop38.payload (types base) p 0 28) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box ops runtime world
    PV_RunJoin_FieldValidation73.Cells bytes 28#usize := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  intro i hi
  have hlen : bytes.length=896 := by
    change bytes.val.length=896
    rw [value,PV_RunJoin_PolyLoop38.payload_length]
  have offsets := PV_RunJoin_PolyOffsets73.offsets i hi
  obtain ⟨s,hs,hv,hl⟩ := PV_RunJoin_ByteSlice40.range bytes
    (Usize.wrapping_mul 32#usize i)
    (Usize.wrapping_add (Usize.wrapping_mul 32#usize i) 32#usize)
    (by rw [offsets.1,offsets.2];omega) (by rw [offsets.2,hlen];omega)
  obtain ⟨w,window,canonical,high⟩ :=
    PV_RunJoin_PolyPayloadCanonicalWindow73.complete p 0 28 i.val hi
  have sw : s=Array.to_slice (PV_RunJoin_FlatBytes35.wire w) := by
    apply Subtype.ext
    rw [hv,offsets.1,offsets.2,value]
    have sub : 32*i.val+32-32*i.val=32 := by omega
    rw [sub]
    exact window
  obtain ⟨parsed,zero⟩ := PV_RunJoin_NativeCanonicalParse73.complete
    base heap box ops runtime world w canonical high
  exact ⟨s,w,hs,by rw [sw];exact parsed,zero⟩

#print axioms complete
end R1Z.PV_RunJoin_NativePolynomialWindows73
