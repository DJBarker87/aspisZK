import R1Z.PDict_FileFlush
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_FileCarrier
open Aeneas Aeneas.Std Result ProverRwFull
/-- Value view of a live Unix File owner. The native world supplies ownership;
this subtype does not create OS authority. P6's full descriptor codec checks
cover every valid owner value. File Drop closes this descriptor once, with an
arbitrary OS reply; that effect is not erased by this value interpretation. -/
def File := { fd : I32 // 0 ≤ fd.val }
def descriptor (file : File) : I32 := file.val
def ofDescriptor (fd : I32) (valid : 0 ≤ fd.val) : File := ⟨fd,valid⟩
@[reducible] def native (base : ExternalTypes) : ExternalTypes :=
  PDict_FileFlush.native { base with op0 := File }
@[reducible] def selected (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) : @ExternalFuns (native base) :=
  PDict_FileFlush.selected { base with op0 := File } ops

theorem type0_installed (base : ExternalTypes) : (native base).op0 = File := rfl

theorem descriptor_valid (file : File) : 0 ≤ (descriptor file).val := file.property

theorem descriptor_roundtrip (fd : I32) (valid : 0 ≤ fd.val) :
    descriptor (ofDescriptor fd valid) = fd := rfl

theorem owner_value_roundtrip (file : File) :
    ofDescriptor (descriptor file) (descriptor_valid file) = file := rfl

theorem descriptor_injective : Function.Injective descriptor := by
  intro a b h
  exact Subtype.ext h

theorem op17_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) (file : File) :
    (selected base ops).op17 file = .ok (.Ok (),file) := rfl

theorem flush_descriptor_frame (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) (file : File) :
    (do let (_,next) ← (selected base ops).op17 file
        .ok (descriptor next)) = .ok (descriptor file) := rfl

#print axioms type0_installed
#print axioms descriptor_valid
#print axioms descriptor_roundtrip
#print axioms owner_value_roundtrip
#print axioms descriptor_injective
#print axioms op17_installed
#print axioms flush_descriptor_frame
end R1Z.PDict_FileCarrier
