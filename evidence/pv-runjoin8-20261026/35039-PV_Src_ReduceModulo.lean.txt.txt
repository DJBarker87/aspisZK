import R1Z.PV_Src_ScalarReduce

/-! Equality of the wrapping release reducer and the retained modulo-based
copy, for all U64 values. This permits symbolic callee substitution. -/
set_option autoImplicit false
namespace R1Z.PV_Src_ReduceModulo
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine

def remainder (x : U64) : U32 :=
  UScalar.cast .U32 (⟨BitVec.umod x.bv (UScalar.cast .U64 R0PoseidonCopy.P).bv⟩ : U64)

theorem value (x : U64) : (remainder x).val = x.val % 2147483647 := by
  have hm : (⟨BitVec.umod x.bv (UScalar.cast .U64 R0PoseidonCopy.P).bv⟩ : U64).val = x.val % 2147483647 := by
    rw [umod_val,p64]
  rw [remainder,c32 _ (by rw [hm];have := Nat.mod_lt x.val (by decide : 0 < 2147483647);omega),hm]

theorem word_eq (x : U64) : PV_Src_ScalarReduce.value x = remainder x := by
  apply UScalar.eq_of_val_eq
  rw [PV_Src_ScalarReduce.modulo,value]

theorem reference (x : U64) :
    AspisBuilderPoseidonReference.aspis_core.field.M31.reduce_u62 x =
      (do let r ← x % (UScalar.cast .U64 R0PoseidonCopy.P); ok (UScalar.cast .U32 r)) := by
  rw [PV_Src_ScalarReduce.reference_eq,
    rem_ok x (UScalar.cast .U64 R0PoseidonCopy.P) (by rw [p64];decide)]
  simp only [bind_tc_ok]
  exact congrArg Result.ok (word_eq x)

#print axioms value
#print axioms word_eq
#print axioms reference
end R1Z.PV_Src_ReduceModulo
