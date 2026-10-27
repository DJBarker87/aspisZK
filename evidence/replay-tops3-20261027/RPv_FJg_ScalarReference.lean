import RPv_FJg_ScalarValue
import RPu_FJc_PermTable
import RPu_FIp_PowersValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJg_ScalarReference
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NQ NE wide)
open scoped BigOperators

theorem sumPrefix (p : Array NE 4#usize) (f : Array NQ 4#usize) (n : Nat) :
    FJg_ScalarCell.sumPrefix p f n=∑ j∈Finset.range n,FJg_ScalarCell.term p f j := by
  induction n with
  | zero => simp only [FJg_ScalarCell.sumPrefix,Finset.range_zero,Finset.sum_empty]
  | succ n ih => rw [FJg_ScalarCell.sumPrefix,Finset.sum_range_succ,ih]

/-- Scalar factor on SAME powers4 output, including PERM and quarter. -/
theorem value (a : NE) (p : Array NE 4#usize) (f : Array NQ 4#usize)
    (ha : FIo_WideValues.Canon a) (hp : FIo_Native.weights.powers 4#usize a=ok p)
    (out : NE) (run : FIo_Native.weights.Weights.scalar_factor f p=ok out) :
    FIo_WideValues.Canon out ∧ decodeWide (wide out)=decodeM FIo_Native.weights.QUARTER •
      ∑ j∈Finset.range 4,decodeWide (wide a)^FJc_LowModel.perm j*
        algebraMap OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E (FJf_QMArray.value f j) := by
  have powers := FIp_PowersValue.powers 4#usize a p ha hp
  have scalar := FJg_ScalarValue.value p f powers.1 out run
  refine ⟨scalar.1,?_⟩
  rw [scalar.2,sumPrefix]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [FJg_ScalarCell.term,powers.2 _ (FJc_PermTable.bound j (Finset.mem_range.mp hj))]
#print axioms sumPrefix
#print axioms value
end AspisR1.FJg_ScalarReference
end
