import RPu_FJm_LibraModel
import RPu_FJg_ScalarReference
import RPu_FJm_LibraTermValue
import RPu_FJg_Quarter
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_LibraFactors
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NQ NE wide qm)
open scoped BigOperators
abbrev FK := OraclePortCheckpointAbiC5.K
abbrev FE := OraclePortCheckpointAbiC5.E
attribute [local irreducible] QuadraticAlgebra.instInv

theorem low (a : NE) (ap : Array NE 4#usize) (base : Array NQ 4#usize) (q : FK)
    (ca : FIo_WideValues.Canon a) (hp : FIo_Native.weights.powers 4#usize a=ok ap)
    (hb : ∀ s : Fin 4,FJf_QMArray.value base s.val=q^s.val)
    (out : NE) (run : FIo_Native.weights.Weights.scalar_factor base ap=ok out) :
    FIo_WideValues.Canon out ∧ decodeWide (wide out)=
      FJm_LibraModel.low (algebraMap FK FE q) (decodeWide (wide a)) := by
  have v := FJg_ScalarReference.value a ap base ca hp out run
  refine ⟨v.1,?_⟩
  rw [v.2,←Fin.sum_univ_eq_sum_range]
  rw [FJg_Quarter.value]
  unfold FJm_LibraModel.low FJg_DualTensor.low
  apply congrArg (fun x : FE => RoundPairing.quarter*x)
  apply Finset.sum_congr rfl
  intro s _
  rw [hb s,map_pow]
  have perm : FJc_LowModel.perm s.val=(4-s.val)%4 := by
    rw [FJc_PermTable.formula _ s.isLt]; split <;> omega
  rw [perm,mul_comm]

theorem term (a : NE) (ap : Array NE 4#usize) (high : Array NQ 4#usize) (q : FK)
    (ca : FIo_WideValues.Canon a) (hp : FIo_Native.weights.powers 4#usize a=ok ap)
    (hh : ∀ s : Fin 4,FJf_QMArray.value high s.val=q^(4*s.val))
    (s : Fin 4) (j i : Usize) (out : NE) (hj : j.val=s.val)
    (run : FJm_LibraStages.term ap high j=ok (i,out)) :
    i.val=(4-s.val)%4 ∧ FIo_WideValues.Canon out ∧
      decodeWide (wide out)=FJm_LibraModel.term (algebraMap FK FE q) (decodeWide (wide a)) s := by
  have powers := FIp_PowersValue.powers 4#usize a ap ca hp
  have v := FJm_LibraTermValue.value ap high j i out powers.1 run
  have perm : FJc_LowModel.perm s.val=(4-s.val)%4 := by rw [FJc_PermTable.formula _ s.isLt]; split <;> omega
  have bound : FJc_LowModel.perm s.val < (4#usize).val := by
    change FJc_LowModel.perm s.val < 4
    exact FJc_PermTable.bound _ s.isLt
  refine ⟨by simpa only [hj,perm] using v.1,v.2.1,?_⟩
  rw [v.2.2,hj,powers.2 _ bound,hh s,map_pow,perm]
  unfold FJm_LibraModel.term
  ring

#print axioms low
#print axioms term
end AspisR1.FJr_LibraFactors
end
