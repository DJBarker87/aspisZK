import NHE_ParsePort
set_option autoImplicit false
namespace NHE_BytePort
open Aeneas Aeneas.Std Result AspisR1
open NHE_ParsePort

theorem bytes (input : Slice U8) :
 FIo_FieldBridge.map (Option.map record) (FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes input)=
 AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes input := by
 unfold FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
 simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.BYTE_LEN,AspisR1RecordParser.field.wide_exact.WideExact.BYTE_LEN]
 split
 · rfl
 · simp only [lift,bind_tc_ok,FIo_FieldBridge.map_bind,NHE_ParsePort.limbs]

#print axioms bytes
end NHE_BytePort
