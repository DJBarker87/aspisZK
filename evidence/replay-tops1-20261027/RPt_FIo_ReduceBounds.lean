import RPt_FIo_ReduceFacts
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.FIo_ReduceBounds

def fold (x : U64) : U64 :=
  U64.wrapping_add (x &&& (2147483647#u64)) (U64.wrapping_shr x (31#u32))

theorem shr_val (x : U64) : (U64.wrapping_shr x (31#u32)).val=x.val/2147483648 := by
  change (x.bv >>> (31 : Nat)).toNat=x.bv.toNat/2147483648
  rw [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]

theorem shr_bound (x : U64) : (U64.wrapping_shr x (31#u32)).val≤8589934591 := by
  rw [shr_val]
  have hx := x.hSize
  scalar_tac

theorem sum_bound (x : U64) :
    (x &&& (2147483647#u64)).val+(U64.wrapping_shr x (31#u32)).val<UScalar.size .U64 := by
  have a := FIo_ReduceFacts.low x
  have b := shr_bound x
  scalar_tac

theorem checked (x : U64) :
    (x &&& (2147483647#u64))+(U64.wrapping_shr x (31#u32))=ok (fold x) :=
  FIo_ScalarBridge.add _ _ (sum_bound x)

#print axioms shr_val
#print axioms shr_bound
#print axioms sum_bound
#print axioms checked
end AspisR1.FIo_ReduceBounds
