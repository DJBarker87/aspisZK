import EbyKPushTotalityV1
import FinishDotCountBoundV3
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S5EbyKPushCountInvariantProductUpdateV1
open AspisR1S5EbyKPushTotalityV1

/-- The retained count invariant supplies the two exact pre-call accumulator
bounds required by the QRaw decoded update theorem. The call itself is the
same concrete emitted QRaw-backed EbyK push, and scalar acceptance remains the
actual source predicate. -/
theorem push_success_product_update_of_count_invariant
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
  have hcountNat : self.count.val < 4096 := by
    simpa [AspisR1EbyKPushExplicitOpsV1.maxTerms] using hcount
  have hacc0 : ∀ x ∈ self.c0.sums.val, x.val < 2^46 := by
    intro x hx
    have hex := List.mem_iff_getElem.mp hx
    rcases hex with ⟨i,hi,hix⟩
    subst x
    have hi4 : i < 4 := by simpa [self.c0.sums.property] using hi
    exact AspisR1FinishDotCountBoundV2.count_bound_to_preaccumulator
      self.count.val self.c0.sums hcountNat hinv0 i hi4
  have hacc1 : ∀ x ∈ self.c1.sums.val, x.val < 2^46 := by
    intro x hx
    have hex := List.mem_iff_getElem.mp hx
    rcases hex with ⟨i,hi,hix⟩
    subst x
    have hi4 : i < 4 := by simpa [self.c1.sums.property] using hi
    exact AspisR1FinishDotCountBoundV2.count_bound_to_preaccumulator
      self.count.val self.c1.sums hcountNat hinv1 i hi4
  exact push_success_product_update_of_valid_scalar self value scalar
    hcanonical hcount hscalar hacc0 hacc1

#print axioms push_success_product_update_of_count_invariant
end AspisR1S5EbyKPushCountInvariantProductUpdateV1
