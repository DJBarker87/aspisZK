import NMX_U64Byte0
import NMX_U64Byte1
import NMX_U64Byte2
import NMX_U64Byte3
import NMX_U64Byte4
import NMX_U64Byte5
import NMX_U64Byte6
import NMX_U64Byte7
import NMX_U64Model
set_option autoImplicit false
namespace NMX_U64Carrier
open Aeneas Aeneas.Std NMX_Carrier

theorem entry (x : U64) (i : Nat) (bound : i < 8) :
 byte ((core.num.U64.to_le_bytes x).val.getD i 0#u8) =
 (long x >>> UInt64.ofNat (8*i)).toUInt8 := by
 apply UInt8.toNat_inj.mp
 rw [NMX_U64Model.value x i bound]
 interval_cases i <;> simp only [NMX_U64Byte0.value,NMX_U64Byte1.value,NMX_U64Byte2.value,NMX_U64Byte3.value,NMX_U64Byte4.value,NMX_U64Byte5.value,NMX_U64Byte6.value,NMX_U64Byte7.value,Nat.reducePow]

theorem value (x : U64) :
 bytes (Array.to_slice (core.num.U64.to_le_bytes x)) = RSL.u64le (long x) := by
 have layout : bytes (Array.to_slice (core.num.U64.to_le_bytes x)) =
 [byte ((core.num.U64.to_le_bytes x).val.getD 0 0#u8),
  byte ((core.num.U64.to_le_bytes x).val.getD 1 0#u8),
  byte ((core.num.U64.to_le_bytes x).val.getD 2 0#u8),
  byte ((core.num.U64.to_le_bytes x).val.getD 3 0#u8),
  byte ((core.num.U64.to_le_bytes x).val.getD 4 0#u8),
  byte ((core.num.U64.to_le_bytes x).val.getD 5 0#u8),
  byte ((core.num.U64.to_le_bytes x).val.getD 6 0#u8),
  byte ((core.num.U64.to_le_bytes x).val.getD 7 0#u8)] := by
  change (core.num.U64.to_le_bytes x).val.map byte = _
  rw [NMX_U64Layout.value]
  rfl
 rw [layout,entry x 0 (by decide),entry x 1 (by decide),entry x 2 (by decide),entry x 3 (by decide),entry x 4 (by decide),entry x 5 (by decide),entry x 6 (by decide),entry x 7 (by decide)]
 rfl
#print axioms entry
#print axioms value
end NMX_U64Carrier
