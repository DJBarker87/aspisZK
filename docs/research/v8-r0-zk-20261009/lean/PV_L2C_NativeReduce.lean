import PV_L2C_Reducer
import R1Z.PV_Src_ReduceModulo
set_option autoImplicit false
namespace PV_L2C_NativeReduce
open Aeneas Aeneas.Std Result PV_L2C_M31 PV_L2C_Reducer

/-- Literal width-64 mask/shift/add step of field/ct.rs::reduce64. -/
def fold (x : BitVec 64) : BitVec 64 :=
  (x &&& BitVec.ofNat 64 p) + (x >>> 31)

theorem mask_value (x : BitVec 64) :
    (x &&& BitVec.ofNat 64 p).toNat = x.toNat % (p+1) := by
  rw [BitVec.toNat_and]
  change x.toNat &&& (2^31-1) = x.toNat % 2^31
  exact Nat.and_two_pow_sub_one_eq_mod _ _
#print axioms mask_value

theorem fold_value (x : BitVec 64) : (fold x).toNat = fold31 x.toNat := by
  have hb := first_bound x.toNat x.isLt
  unfold fold
  rw [BitVec.toNat_add,mask_value,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  change (x.toNat % (p+1) + x.toNat / (p+1)) % 2^64 = fold31 x.toNat
  change fold31 x.toNat % 2^64 = fold31 x.toNat
  apply Nat.mod_eq_of_lt
  unfold p at hb
  omega
#print axioms fold_value

theorem narrowed_value (x : BitVec 64) :
    ((fold (fold x)).setWidth 32).toNat = fold31 (fold31 x.toNat) := by
  rw [BitVec.toNat_setWidth,fold_value,fold_value]
  apply Nat.mod_eq_of_lt
  have hb := second_bound x.toNat x.isLt
  unfold p at hb
  omega
#print axioms narrowed_value

def run (x : BitVec 64) : word := subtractP ((fold (fold x)).setWidth 32)

theorem canonical_result (x : BitVec 64) : canonical (run x) := by
  apply subtractP_canonical
  rw [narrowed_value]
  exact reduction_bound x.toNat x.isLt
#print axioms canonical_result

theorem field_result (x : BitVec 64) : decode (run x) = (x.toNat : ZMod p) := by
  rw [run,subtractP_decode]
  change (((fold (fold x)).setWidth 32).toNat : ZMod p) = _
  rw [narrowed_value,fold_decode,fold_decode]
#print axioms field_result

theorem value (x : BitVec 64) : (run x).toNat = x.toNat % p := by
  have he := congrArg ZMod.val (field_result x)
  change (run x).toNat % p = x.toNat % p at he
  rw [Nat.mod_eq_of_lt (canonical_result x)] at he
  exact he
#print axioms value

/-- Exact raw-word agreement with the already extracted owned external-layer
reducer, completing the scalar value cut without a Kani field-arithmetic gate. -/
theorem reference (x : U64) :
    AspisBuilderPoseidonReference.aspis_core.field.M31.reduce_u62 x =
      ok (⟨run x.bv⟩ : U32) := by
  rw [R1Z.PV_Src_ScalarReduce.reference_eq]
  congr 1
  apply UScalar.eq_of_val_eq
  rw [R1Z.PV_Src_ScalarReduce.modulo]
  exact (value x.bv).symm
#print axioms reference
end PV_L2C_NativeReduce
