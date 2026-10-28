import R1Z.PV_RunJoin_FlatBytes35
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ZeroWord40
open Aeneas Aeneas.Std
/-- Four fixed zero bytes only; no field or polynomial reduction. -/
theorem bytes : (core.num.U32.to_le_bytes 0#u32).val=[0#u8,0#u8,0#u8,0#u8] := by
  change (0#u32).bv.toLEBytes.map (@UScalar.mk .U8) = _
  rw [BitVec.toLEBytes.eq_1]
  norm_num only
  rw [BitVec.toLEBytes.eq_1]
  norm_num only
  rw [BitVec.toLEBytes.eq_1]
  norm_num only
  rw [BitVec.toLEBytes.eq_1]
  norm_num only
  rw [BitVec.toLEBytes.eq_1]
  norm_num only
  rfl
#print axioms bytes
end R1Z.PV_RunJoin_ZeroWord40
