import FJg_ScalarReference
import FJj_LowSum
import FJj_TensorPrefix
import FJg_Permutation
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_RowScale
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NQ NE wide)
open scoped BigOperators
abbrev FK := OraclePortCheckpointAbiC5.K
abbrev FE := OraclePortCheckpointAbiC5.E
attribute [local irreducible] QuadraticAlgebra.instInv FJg_DualTensor.low

theorem value (row : Array (Array NQ 4#usize) 5#usize) (digit : Array NQ 4#usize)
    (factors : Fin 5 → Fin 4 → FK)
    (values : ∀ (d : Fin 5) (s : Fin 4),FJj_TensorPrefix.rowValue row d.val s.val=factors d s)
    (d : Fin 5) (di : Usize) (hdi : di.val=d.val) (hd : Array.index_usize row di=ok digit)
    (a : NE) (p : Array NE 4#usize) (ha : FIo_WideValues.Canon a)
    (hp : FIo_Native.weights.powers 4#usize a=ok p) :
    decodeM FIo_Native.weights.QUARTER • FJg_ScalarCell.sumPrefix p digit 4=
      FJg_DualTensor.low (fun s=>algebraMap FK FE (factors d s)) (decodeWide (wide a)) := by
  have powers := FIp_PowersValue.powers 4#usize a p ha hp
  have dv : ∀ s : Fin 4,FJf_QMArray.value digit s.val=factors d s := by
    intro s
    have read := FJj_TensorPrefix.read row di digit hd s.val
    rw [hdi,values d s] at read
    exact read.symm
  have terms : FJg_ScalarCell.sumPrefix p digit 4=∑ s : Fin 4,
      algebraMap FK FE (factors d s)*decodeWide (wide a)^((4-s.val)%4) := by
    rw [FJg_ScalarReference.sumPrefix,←Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro s _
    rw [FJg_ScalarCell.term,powers.2 _ (FJc_PermTable.bound s.val s.isLt),dv s,FJg_Permutation.value]
    ring
  rw [terms]
  exact FJj_LowSum.value _ _

#print axioms value
end AspisR1.FJr_RowScale
end
