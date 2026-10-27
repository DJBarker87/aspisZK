import KSA_SmallFields
open Aeneas Aeneas.Std Result XRn_Join_Release XRn_Join_FieldExternal
set_option autoImplicit false
namespace KSA.Bytes

theorem qm_zero : aspis_core.field.QM31.from_le_bytes
    ((Array.repeat 16#usize 0#u8).to_slice) = ok (some qzero) := by rfl
theorem qm_short : aspis_core.field.QM31.from_le_bytes
    ((Array.repeat 0#usize 0#u8).to_slice) = ok none := by rfl
theorem wide_limbs : aspis_core.field.wide_exact.WideExact.from_limbs
    (Array.repeat 8#usize 0#u32) = ok (some Small.wz) := by rfl
theorem wide_to_limbs : aspis_core.field.wide_exact.WideExact.to_limbs Small.wz =
    ok (Array.repeat 8#usize 0#u32) := by rfl
theorem wide_bytes : aspis_core.field.wide_exact.WideExact.from_le_bytes
    ((Array.repeat 32#usize 0#u8).to_slice) = ok (some Small.wz) := by rfl
theorem wide_short : aspis_core.field.wide_exact.WideExact.from_le_bytes
    ((Array.repeat 0#usize 0#u8).to_slice) = ok none := by rfl
theorem wide_to_bytes : aspis_core.field.wide_exact.WideExact.to_le_bytes Small.wz =
    ok (Array.repeat 32#usize 0#u8) := by rfl
theorem from_m31_p : aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31
    2147483647#u32 = ok Small.wz := by rfl
theorem compact_empty : compact.check_values ((Array.repeat 0#usize 0#u8).to_slice) = ok (.Ok ()) := by rfl
theorem echeck_empty : verifier.echeck ((Array.repeat 0#usize 0#u8).to_slice) true = ok (.Ok ()) := by rfl
theorem validate_empty : r1_wire.validate_record_fields 14#u8
    ((Array.repeat 0#usize 0#u8).to_slice) = ok (.Ok ()) := by rfl
theorem expand_empty : compact.expand_values
    ((Array.repeat 0#usize 0#u8).to_slice) ((Array.repeat 0#usize 0#u8).to_slice) =
    ok (.Ok (),((Array.repeat 0#usize 0#u8).to_slice)) := by
  conv => lhs; cbv
  rfl
theorem decode_bad_row : r1_wire.ValidatedRecord.decode_k 0#usize
    ⟨0#u8,((Array.repeat 0#usize 0#u8).to_slice)⟩ 0#usize = ok (.Err .InvalidRow) := by rfl

#print axioms qm_zero
#print axioms qm_short
#print axioms wide_limbs
#print axioms wide_to_limbs
#print axioms wide_bytes
#print axioms wide_short
#print axioms wide_to_bytes
#print axioms from_m31_p
#print axioms compact_empty
#print axioms echeck_empty
#print axioms validate_empty
#print axioms expand_empty
#print axioms decode_bad_row
end KSA.Bytes
