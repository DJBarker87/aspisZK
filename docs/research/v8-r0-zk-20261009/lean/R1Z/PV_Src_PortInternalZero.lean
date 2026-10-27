import R1Z.PV_Src_PortInternalField

/-! The first internal-linear lane uses part_sum + P - state[0]. The input
canonicality premise is precisely what prevents the source subtraction wrapping. -/
set_option autoImplicit false
namespace R1Z.PV_Src_PortInternalZero
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open BuilderForestAdmissionPort

def cell (part : U64) (first : U32) : U32 := PV_Src_ScalarReduce.value
  (U64.wrapping_sub (U64.wrapping_add part (UScalar.cast .U64 aspis_core.field.P))
    (UScalar.cast .U64 first))

theorem value (part : U64) (first : U32)
    (hp : part.val < 68719476736) (hf : first.val < 2147483647) :
    (cell part first).val = (part.val + 2147483647 - first.val) % 2147483647 := by
  have pval : (UScalar.cast .U64 aspis_core.field.P).val = 2147483647 := by
    rw [c64,aspis_core.field.P]
    rfl
  have hadd := add64v part (UScalar.cast .U64 aspis_core.field.P)
    part.val 2147483647 rfl pval (by omega)
  have hsub := sub64 (U64.wrapping_add part (UScalar.cast .U64 aspis_core.field.P))
    (UScalar.cast .U64 first) (by rw [hadd,c64];omega)
  unfold cell
  rw [PV_Src_ScalarReduce.modulo,hsub,hadd,c64]

variable {K : Type} [Field K] [CharP K 2147483647]

theorem lift (part : U64) (first : U32)
    (hp : part.val < 68719476736) (hf : first.val < 2147483647) :
    liftU (K := K) (cell part first) = (part.val : K) - liftU first := by
  unfold liftU
  rw [value part first hp hf,cast_mod,Nat.cast_sub (by omega),Nat.cast_add,
    CharP.cast_eq_zero K 2147483647,add_zero]

#print axioms value
#print axioms lift
end R1Z.PV_Src_PortInternalZero
