import R1Z.PV_RunJoin_SourceArithmeticLift
set_option autoImplicit false
namespace R1Z.PV_RunJoin_SourceScalar
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_Src_ScalarFold
variable {K : Type} [Field K] [CharP K 2147483647]

/-- Exact reducer body in the ACTUAL forest extraction; the owned external
helper's namespace is not silently substituted for this source definition. -/
theorem forest_reduce_eq (x : U64) :
    BuilderForestAdmissionPort.aspis_core.field.reduce_u64 x =
      ok (PV_Src_ScalarReduce.value x) := by
  simp only [BuilderForestAdmissionPort.aspis_core.field.reduce_u64,
    BuilderForestAdmissionPort.aspis_core.field.P,lift,bind_tc_ok,
    PV_Src_ScalarReduce.value,fold,mask]
  split <;> rfl

/-- All raw U32 multiplicands are admitted. Their U64 product cannot wrap,
and the source reducer supplies canonical words and the exact field product. -/
theorem forest_mul (a b : U32) :
    ∃ out, BuilderForestAdmissionPort.aspis_core.field.M31.mul a b = ok out ∧
      out.val < 2147483647 ∧ liftU (K := K) out = liftU a * liftU b := by
  let product := U64.wrapping_mul (UScalar.cast .U64 a) (UScalar.cast .U64 b)
  refine ⟨PV_Src_ScalarReduce.value product,?_,PV_Src_ScalarReduce.canonical product,?_⟩
  · rw [BuilderForestAdmissionPort.aspis_core.field.M31.mul]
    simp only [lift,bind_tc_ok,forest_reduce_eq,product]
  · change ((PV_Src_ScalarReduce.value (U64.wrapping_mul (UScalar.cast .U64 a)
      (UScalar.cast .U64 b))).val : K) = _
    rw [PV_Src_ScalarReduce.modulo,cast_mod,mul2_val]
    simp only [Nat.cast_mul,liftU]

/-- Source addition/subtraction retain the exact canonical-copy Result,
including the source comparison and wrapping operations. -/
theorem forest_add_copy (a b : U32) :
    BuilderForestAdmissionPort.aspis_core.field.M31.add a b = R0BlockCopies.m31_add a b := by
  simp only [BuilderForestAdmissionPort.aspis_core.field.M31.add,
    BuilderForestAdmissionPort.aspis_core.field.P,R0BlockCopies.m31_add,R0BlockCopies.P,
    lift,bind_tc_ok]

theorem forest_sub_copy (a b : U32) :
    BuilderForestAdmissionPort.aspis_core.field.M31.sub a b = R0BlockCopies.m31_sub a b := by
  simp only [BuilderForestAdmissionPort.aspis_core.field.M31.sub,
    BuilderForestAdmissionPort.aspis_core.field.P,R0BlockCopies.m31_sub,R0BlockCopies.P,
    lift,bind_tc_ok]

theorem forest_add (a b : U32) (ha : a.val < 2147483647) (hb : b.val < 2147483647) :
    ∃ out, BuilderForestAdmissionPort.aspis_core.field.M31.add a b = ok out ∧
      out.val < 2147483647 ∧ liftU (K := K) out = liftU a + liftU b := by
  obtain ⟨out,run,value⟩ := R0Z.WriterRefine.m31_add_spec a b ha hb
  refine ⟨out,(forest_add_copy a b).trans run,?_,?_⟩
  · rw [value]
    split <;> omega
  · change (out.val : K) = (a.val : K)+(b.val : K)
    rw [value]
    by_cases h : 2147483647 ≤ a.val+b.val
    · rw [if_pos h,Nat.cast_sub h,CharP.cast_eq_zero K 2147483647,sub_zero,Nat.cast_add]
    · rw [if_neg h,Nat.cast_add]

theorem forest_sub (a b : U32) (ha : a.val < 2147483647) (hb : b.val < 2147483647) :
    ∃ out, BuilderForestAdmissionPort.aspis_core.field.M31.sub a b = ok out ∧
      out.val < 2147483647 ∧ liftU (K := K) out = liftU a - liftU b := by
  obtain ⟨out,run,value⟩ := R0Z.WriterRefine.m31_sub_spec_wide a b ha hb
  refine ⟨out,(forest_sub_copy a b).trans run,?_,?_⟩
  · rw [value]
    split <;> omega
  · change (out.val : K) = (a.val : K)-(b.val : K)
    rw [value]
    by_cases h : b.val ≤ a.val
    · rw [if_pos h,Nat.cast_sub h]
    · rw [if_neg h,Nat.cast_sub (show b.val ≤ a.val+2147483647 by omega),
        Nat.cast_add,CharP.cast_eq_zero K 2147483647,add_zero]

#print axioms forest_reduce_eq
#print axioms forest_mul
#print axioms forest_add_copy
#print axioms forest_sub_copy
#print axioms forest_add
#print axioms forest_sub
end R1Z.PV_RunJoin_SourceScalar
