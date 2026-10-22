import EbyKPushCountInvariantProductUpdateV1
import EbyKPushDotBackend
import FinishDotCountBoundV3
import S5QRaw.EbyKPushDecodedProductUpdateV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S5EbyKPushStateInvariantStepV1
open AspisR1S5EbyKPushTotalityV1

/-- One successful valid-scalar EbyK push preserves both count-indexed Dot
invariants, increments the actual checked count by one, and advances both
decoded accumulators by the two actual QRaw products. All conclusions share
the same returned state. -/
theorem push_success_state_step
    (self : State) (value : Wide) (scalar : Qm)
    (hcanonical : AspisR1EbyKPowerValueCanonicalToPush.pushCanonical value)
    (hcount : self.count < AspisR1EbyKPushExplicitOpsV1.maxTerms)
    (hscalar : ∀ x ∈ (AspisR1EbyKPushDotBackend.scalarQ scalar).val,
      x.val < 2147483647)
    (hinv0 : AspisR1FinishDotCountBoundV2.sumsBelowCount self.count.val self.c0.sums)
    (hinv1 : AspisR1FinishDotCountBoundV2.sumsBelowCount self.count.val self.c1.sums) :
    ∃ out,
      AspisR1EbyKPushDotBackend.pushWithDotBackend QRaw self value scalar =
        .ok (.Ok (),out) ∧
      AspisR1FinishDotCountBoundV2.sumsBelowCount out.count.val out.c0.sums ∧
      AspisR1FinishDotCountBoundV2.sumsBelowCount out.count.val out.c1.sums ∧
      out.count.val = self.count.val + 1 ∧
      AspisR1EbyKPushDecodedProductUpdate.castSums out.c0.sums =
        AspisR1EbyKPushDecodedProductUpdate.tupleAdd
          (AspisR1EbyKPushDecodedProductUpdate.castSums self.c0.sums)
          (AspisR1.R22RawQmProductResidues.qmulCoefficients
            ((value.c0.c0.a.val,value.c0.c0.b.val),
             (value.c0.c1.a.val,value.c0.c1.b.val))
            ((scalar.c0.a.val,scalar.c0.b.val),
             (scalar.c1.a.val,scalar.c1.b.val))) ∧
      AspisR1EbyKPushDecodedProductUpdate.castSums out.c1.sums =
        AspisR1EbyKPushDecodedProductUpdate.tupleAdd
          (AspisR1EbyKPushDecodedProductUpdate.castSums self.c1.sums)
          (AspisR1.R22RawQmProductResidues.qmulCoefficients
            ((value.c1.c0.a.val,value.c1.c0.b.val),
             (value.c1.c1.a.val,value.c1.c1.b.val))
            ((scalar.c0.a.val,scalar.c0.b.val),
             (scalar.c1.a.val,scalar.c1.b.val))) := by
  obtain ⟨out,hrun,hprod0,hprod1⟩ :=
    AspisR1S5EbyKPushCountInvariantProductUpdateV1.push_success_product_update_of_count_invariant
      self value scalar hcanonical hcount hscalar hinv0 hinv1
  have hbound :=
    AspisR1FinishDotCountBoundV2.successful_push_preserves_count_bound
      QRaw self value scalar out hinv0 hinv1 hrun
  obtain ⟨hinv0',hinv1',_hcount_le,_hpre0,_hpre1⟩ := hbound
  obtain ⟨_lo,_hi,_hlo,_hhi,_hs0,_hs1,_hguard,hinc,_hscalar⟩ :=
    AspisR1EbyKPushDotBackend.successful_push_exact_backend
      QRaw self value scalar out hrun
  exact ⟨out,hrun,hinv0',hinv1',hinc,hprod0,hprod1⟩

#print axioms push_success_state_step
end AspisR1S5EbyKPushStateInvariantStepV1
