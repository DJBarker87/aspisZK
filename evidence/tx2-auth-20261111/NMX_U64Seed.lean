import NMX_ScalarCarrier
set_option autoImplicit false
namespace NMX_U64Seed
open Aeneas Aeneas.Std NMX_Carrier NMX_ScalarCarrier
/-- The actual std u64 little-endian PDA seed. This is not either phantom
field/wide-exact ledger edge. Eight symbolic byte positions only. -/
theorem source (x : U64) :
 (core.num.U64.to_le_bytes x).val.map byte = RSL.u64le (long x) := by
 apply List.ext_getElem
 · simp [RSL.u64le,core.num.U64.to_le_bytes]
 · intro i hi hj
   have size : ((core.num.U64.to_le_bytes x).val.map byte).length = 8 := by
    simpa using (core.num.U64.to_le_bytes x).property
   have hi8 : i < 8 := by simpa only [size] using hi
   have cases8 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
   rcases cases8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    apply UInt8.toNat_inj.mp <;>
    simp [RSL.u64le,byte,long,core.num.U64.to_le_bytes,
      UScalar.val,BitVec.toLEBytes,BitVec.toNat_setWidth,BitVec.toNat_ushiftRight,
      UInt64.toNat_toUInt8,UInt64.toNat_shiftRight,UInt64.toNat_ofNat',UInt8.toNat_ofNat',
      Nat.shiftRight_eq_div_pow,Nat.mod_eq_of_lt x.hBounds] <;> omega
#print axioms source
end NMX_U64Seed
