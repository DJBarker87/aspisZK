import R1Z.PV_Src_PortMultiply
import R1Z.PV_Src_PortAddition

/-! Field meaning and canonical outputs of actual nonlinear scalar source.
This supports the root-helper hash correspondence without concrete reduction. -/
set_option autoImplicit false
namespace R1Z.PV_Src_PortField
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort
variable {K : Type} [Field K] [CharP K 2147483647]

theorem multiply (a b : U32) :
    ∃ z, aspis_core.field.M31.mul a b = ok z ∧ z.val < 2147483647 ∧
      liftU (K := K) z = liftU a * liftU b := by
  let prod := U64.wrapping_mul (UScalar.cast .U64 a) (UScalar.cast .U64 b)
  let z := PV_Src_ScalarReduce.value prod
  have hz : aspis_core.field.M31.mul a b = ok z := by
    unfold aspis_core.field.M31.mul
    simp only [lift,bind_tc_ok]
    change aspis_core.field.M31.reduce_u62 prod = ok z
    rw [PV_Src_PortReduce.source,PV_Src_ScalarReduce.reference_eq]
  obtain ⟨v,hv,hmodel⟩ := R0Z.PoseidonRefine.mul_lift (K := K) a b
  have he : z = v := Result.ok.inj (hz.symm.trans ((PV_Src_PortMultiply.multiply a b).trans hv))
  refine ⟨z,hz,PV_Src_ScalarReduce.canonical prod,?_⟩
  rw [he]
  exact hmodel

theorem power (a : U32) :
    ∃ z, poseidon2.pow5 a = ok z ∧ z.val < 2147483647 ∧
      liftU (K := K) z = R0P.poseidonPow5 (liftU a) := by
  obtain ⟨s,hs,_,hsv⟩ := multiply (K := K) a a
  obtain ⟨t,ht,_,htv⟩ := multiply (K := K) s s
  obtain ⟨u,hu,huc,huv⟩ := multiply (K := K) t a
  refine ⟨u,?_,huc,?_⟩
  · rw [poseidon2.pow5,hs]
    simp only [bind_tc_ok]
    rw [ht]
    simp only [bind_tc_ok]
    exact hu
  · rw [huv,htv,hsv]
    rfl

theorem addition (a b : U32) (ha : a.val < 2147483647) (hb : b.val < 2147483647) :
    ∃ z, aspis_core.field.M31.add a b = ok z ∧ z.val < 2147483647 ∧
      liftU (K := K) z = liftU a + liftU b := by
  obtain ⟨z,hz,hv,hc⟩ := PV_Src_PortAddition.canonical a b ha hb
  refine ⟨z,hz,hc,?_⟩
  unfold liftU
  rw [hv,R0Z.PoseidonRefine.cast_mod,Nat.cast_add]

#print axioms multiply
#print axioms power
#print axioms addition
end R1Z.PV_Src_PortField
