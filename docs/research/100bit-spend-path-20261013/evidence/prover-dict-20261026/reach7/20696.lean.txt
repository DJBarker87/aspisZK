import R1Z.PDict_CodecDictionary
set_option autoImplicit false
namespace R1Z.PDict_CodecLength
open Aeneas Aeneas.Std Result ProverRwFull

theorem reject_length (bytes : Slice U8) (h : Slice.len bytes ≠ 32#usize) :
    PDict_CodecSource.aspis_core.field.wide_exact.WideExact.from_le_bytes bytes = .ok none := by
  simp [PDict_CodecSource.aspis_core.field.wide_exact.WideExact.from_le_bytes,
    PDict_CodecSource.aspis_core.field.wide_exact.WideExact.BYTE_LEN,h]

theorem selected_reject_length (base : ExternalTypes)
    (ops : @ExternalFuns (PDict_CodecDictionary.native base))
    (bytes : Slice U8) (h : Slice.len bytes ≠ 32#usize) :
    (PDict_CodecDictionary.selected base ops).op50 bytes = .ok none := by
  rw [PDict_CodecDictionary.op50_installed]
  exact reject_length bytes h

#print axioms reject_length
#print axioms selected_reject_length
end R1Z.PDict_CodecLength
