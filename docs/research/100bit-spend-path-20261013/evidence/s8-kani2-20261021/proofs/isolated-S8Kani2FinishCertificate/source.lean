import S8Kani2MutableOutput
import S8Kani2MutableValue
import S8Kani2PrefixIndex
import S8Kani2ReferenceInduction
import S8OwnedP6Certificate

/-! Concrete finite finish certificate. Source correspondence uses the
separately pinned P6 local-iteration receipts, rather than a Lean axiom. -/
set_option autoImplicit false
noncomputable section
namespace S8Kani2FinishCertificate
open Aeneas Aeneas.Std Result
open S8Kani2MutableExtraction.batched_weights
open S8Kani2MutableValue

/-- Total mutable-enumerator traversal and exact pointwise local values.
The only finish precondition is the destination/raw length relation. -/
theorem mutable_finish_total (self : F.BW) (old : FinishSlice)
    (hlen : old.val.length ≤ self.raw.length) :
    ∃ out : FinishSlice,
      BatchedWeights.finish self old = .ok out ∧
      out = prefixWrite (valueAt self) 0 old.len.val old ∧
      ∀ i : Usize, i.val < old.len.val →
        Slice.index_usize out i=.ok (valueAt self i.val) ∧
        F.value self i=.ok (valueAt self i.val) := by
  have hvalue : ∀ i : Usize, i.val < old.len.val →
      F.value self i=.ok (valueAt self i.val) := by
    intro i hi
    apply valueAt_success
    change i.val < old.val.length at hi
    omega
  obtain ⟨out,hrun,hout⟩ := finish_output_invariant self old (valueAt self) hvalue
  refine ⟨out,hrun,hout,?_⟩
  intro i hi
  refine ⟨?_,hvalue i hi⟩
  rw [hout]
  exact S8Kani2PrefixWriteIndex.prefixWrite_index (valueAt self) old.len.val old i le_rfl hi

structure FinishCertificate : Prop where
  reference : S8OwnedP6Certificate.ReferenceCertificate
  finite_reference : ∀ raw old, old.length≤raw.length →
    S8OwnedP6.finish_owned raw old = (do
      let final ← S8Kani2FinishTraversal.steps raw old.length (old,0#usize)
      ok final.1)
  mutable_traversal : ∀ self old, old.val.length≤self.raw.length →
    ∃ out : FinishSlice,
      BatchedWeights.finish self old=.ok out ∧
      out=prefixWrite (valueAt self) 0 old.len.val old ∧
      ∀ i : Usize, i.val<old.len.val →
        Slice.index_usize out i=.ok (valueAt self i.val) ∧
        F.value self i=.ok (valueAt self i.val)

/-- Named P6 Lean-side finish certificate. The packet manifest records the
Kani domains and the remaining caller/source interpretation boundary. -/
theorem finish_certificate : FinishCertificate :=
  ⟨S8OwnedP6Certificate.reference_model,
    S8Kani2ReferenceInduction.reference_finish_induction,mutable_finish_total⟩

#print axioms mutable_finish_total
#print axioms finish_certificate
end S8Kani2FinishCertificate
