import NCI_PendingValue
import S8Kani2MutableValue
import S8Kani2MutableOutput
import S8Kani2PrefixIndex
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCI_FinishCanonical
open Aeneas Aeneas.Std Result
open S8Kani2MutableExtraction.batched_weights

theorem prefix_length (f : Nat → S8Kani2MutableExtraction.aspis_core.field.QM31)
    (start n : Nat) (s : FinishSlice) : (prefixWrite f start n s).val.length=s.val.length := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [prefixWrite]
    rw [ih]
    split <;> simp [Slice.setAtNat]

theorem finish_domains (self : BatchedWeights) (weights : FinishSlice)
    (bound : weights.len.val≤self.raw.length) :
    ∃ result : FinishSlice, BatchedWeights.finish self weights=ok result ∧
      result.val.length=weights.val.length ∧
      ∀ i : Usize, i.val<weights.len.val →
        ∃ q, Slice.index_usize result i=ok q ∧ NCI_PendingValue.Canonical q := by
  let f := S8Kani2MutableValue.valueAt self
  have hvalue : ∀ i : Usize, i.val<weights.len.val → BatchedWeights.value self i=ok (f i.val) := by
    intro i hi
    exact S8Kani2MutableValue.valueAt_success self i (by omega)
  obtain ⟨result,run,contents⟩ := finish_output_invariant self weights f hvalue
  refine ⟨result,run,?_,?_⟩
  · rw [contents]
    exact prefix_length f 0 weights.len.val weights
  · intro i hi
    refine ⟨f i.val,?_,NCI_PendingValue.successful_value self i _ (hvalue i hi)⟩
    rw [contents]
    exact S8Kani2PrefixWriteIndex.prefixWrite_index f weights.len.val weights i (by omega) hi
#print axioms prefix_length
#print axioms finish_domains
end AspisR1.NCI_FinishCanonical
