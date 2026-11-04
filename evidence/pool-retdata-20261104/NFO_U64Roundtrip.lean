import S6ByteInverseV1
set_option autoImplicit false
namespace NFO_U64Roundtrip
open Aeneas Aeneas.Std Result

theorem fromLE_cast {n : Nat} (divisible : n%8=0) {b : BitVec n} {bs : List Byte}
    (same : bs=b.toLEBytes) (width : 8*bs.length=n) :
    (BitVec.fromLEBytes bs).cast width = b := by
  cases same
  rw [BitVec.fromLEBytes_toLEBytes divisible]
  simp

theorem from_to (x : U64) : core.num.U64.from_le_bytes (core.num.U64.to_le_bytes x) = x := by
  have point : ∀ b : Byte, U8.bv (UScalar.mk b) = b := by intro b; rfl
  have map : List.map U8.bv (List.map UScalar.mk x.bv.toLEBytes) = x.bv.toLEBytes := by
    rw [List.map_map]
    simpa [Function.comp_def] using congrArg (fun f : Byte → Byte => List.map f x.bv.toLEBytes) (funext point)
  apply U64.bv_eq_imp_eq
  simp only [core.num.U64.from_le_bytes,core.num.U64.to_le_bytes]
  exact fromLE_cast (by decide : 64%8=0) map _
#print axioms fromLE_cast
#print axioms from_to
end NFO_U64Roundtrip
