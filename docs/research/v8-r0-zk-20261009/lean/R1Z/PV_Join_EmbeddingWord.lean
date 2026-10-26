import R1Z.PV_CB_Op110Source
import R1Z.ProverRwSuccessCtReduce
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_EmbeddingWord
open Aeneas Aeneas.Std Result

theorem mask (x : U64) (bound : x.val < 2147483648) :
    x &&& UScalar.cast .U64 AspisR1ProducerRelease47.field.P = x := by
  apply UScalar.eq_of_val_eq
  rw [UScalar.val_and]
  change x.val &&& (2^31-1) = x.val
  exact Nat.and_two_pow_sub_one_of_lt_two_pow bound

theorem shift (x : U64) (bound : x.val < 2147483648) :
    U64.wrapping_shr x 31#u32 = 0#u64 := by
  apply UScalar.eq_of_val_eq
  change x.val / 2147483648 = 0
  exact Nat.div_eq_of_lt bound

theorem add_zero (x : U64) : U64.wrapping_add x 0#u64 = x := by
  apply UScalar.eq_of_val_eq
  rw [U64.wrapping_add_val_eq]
  change (x.val+0)%2^64 = x.val
  exact Nat.mod_eq_of_lt x.hBounds

theorem narrow_widen (x : U32) : UScalar.cast .U32 (UScalar.cast .U64 x) = x := by
  apply UScalar.eq_of_val_eq
  rw [UScalar.cast_val_eq,U32.cast_U64_val_eq]
  exact Nat.mod_eq_of_lt x.hBounds

/-- Symbolic canonical-word identity, before touching either full embedding. -/
theorem release (x : U32) (bound : x.val < 2147483647) :
    AspisR1ProducerRelease47.field.reduce_u64 (UScalar.cast .U64 x) = ok x := by
  have wide : (UScalar.cast .U64 x).val < 2147483648 := by
    rw [U32.cast_U64_val_eq]
    omega
  have small : ¬ x ≥ AspisR1ProducerRelease47.field.P := by
    change ¬x.val ≥ 2147483647
    omega
  simp only [AspisR1ProducerRelease47.field.reduce_u64,lift,bind_tc_ok,
    mask _ wide,shift _ wide,add_zero,narrow_widen,small,if_neg]

theorem reduce (x : U64) :
    PV_CB_ShippedOp110.aspis_core.field.ct.reduce64 x =
      ProverRwSuccessNativePorts.aspis_core.field.ct.reduce64 x := by
  unfold PV_CB_ShippedOp110.aspis_core.field.ct.reduce64
    ProverRwSuccessNativePorts.aspis_core.field.ct.reduce64
    PV_CB_ShippedOp110.aspis_core.field.ct.subtract_p
    ProverRwSuccessNativePorts.aspis_core.field.ct.subtract_p
    PV_CB_ShippedOp110.aspis_core.field.P
    ProverRwSuccessNativePorts.aspis_core.field.P AspisR1ProducerRelease47.field.P
  rfl

theorem current (x : U32) (bound : x.val < 2147483647) :
    PV_CB_ShippedOp110.aspis_core.field.ct.reduce64 (UScalar.cast .U64 x) = ok x := by
  rw [reduce,ProverRwSuccessCtReduce.reduce]
  exact release x bound

#print axioms mask
#print axioms shift
#print axioms add_zero
#print axioms narrow_widen
#print axioms release
#print axioms reduce
#print axioms current
end R1Z.PV_Join_EmbeddingWord
