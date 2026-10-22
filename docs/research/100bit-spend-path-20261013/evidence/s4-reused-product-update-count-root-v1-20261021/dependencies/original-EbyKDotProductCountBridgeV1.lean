import EbyKDotCountBoundV1
set_option autoImplicit false
namespace AspisR1DotProductCountBridgeV1
open AspisR1DotCountBoundV1

theorem successful_push_product_update_of_count
    (self : AspisR1EbyKPushDotBackend.PushState)
    (value : AspisR1EbyKPushDotBackend.PushWide)
    (scalar : AspisR1EbyKPushDotBackend.PushQm)
    (out : AspisR1EbyKPushDotBackend.PushState)
    (hcanonical : AspisR1EbyKPowerValueCanonicalToPush.pushCanonical value)
    (h0 : sumsBelowCount self.count.val self.c0.sums)
    (h1 : sumsBelowCount self.count.val self.c1.sums)
    (hrun : AspisR1EbyKPushDotBackend.pushWithDotBackend AspisR1EbyKPushDecodedProductUpdate.QRaw self value scalar =
      .ok (.Ok (),out)) :
    AspisR1EbyKPushDecodedProductUpdate.castSums out.c0.sums =
      AspisR1EbyKPushDecodedProductUpdate.tupleAdd
        (AspisR1EbyKPushDecodedProductUpdate.castSums self.c0.sums)
        (AspisR1.R22RawQmProductResidues.qmulCoefficients
          ((value.c0.c0.a.val,value.c0.c0.b.val),
           (value.c0.c1.a.val,value.c0.c1.b.val))
          ((scalar.c0.a.val,scalar.c0.b.val),(scalar.c1.a.val,scalar.c1.b.val))) ∧
    AspisR1EbyKPushDecodedProductUpdate.castSums out.c1.sums =
      AspisR1EbyKPushDecodedProductUpdate.tupleAdd
        (AspisR1EbyKPushDecodedProductUpdate.castSums self.c1.sums)
        (AspisR1.R22RawQmProductResidues.qmulCoefficients
          ((value.c1.c0.a.val,value.c1.c0.b.val),
           (value.c1.c1.a.val,value.c1.c1.b.val))
          ((scalar.c0.a.val,scalar.c0.b.val),(scalar.c1.a.val,scalar.c1.b.val))) := by
  have hstate := successful_push_preserves_count_bound AspisR1EbyKPushDecodedProductUpdate.QRaw self value scalar out h0 h1 hrun
  have hacc0 : ∀ x ∈ self.c0.sums.val, x.val < 2^46 := by
    intro x hx
    have hlt : ∀ j : Nat, ∀ hj : j < 4,
        (self.c0.sums.val[j]'(by rw [self.c0.sums.property]; exact hj)).val < 2^46 := hstate.2.2.2.1
    obtain ⟨j,hj,hxj⟩ := List.mem_iff_getElem.mp hx
    rw [← hxj]
    exact hlt j (by simpa [self.c0.sums.property] using hj)
  have hacc1 : ∀ x ∈ self.c1.sums.val, x.val < 2^46 := by
    intro x hx
    have hlt : ∀ j : Nat, ∀ hj : j < 4,
        (self.c1.sums.val[j]'(by rw [self.c1.sums.property]; exact hj)).val < 2^46 := hstate.2.2.2.2
    obtain ⟨j,hj,hxj⟩ := List.mem_iff_getElem.mp hx
    rw [← hxj]
    exact hlt j (by simpa [self.c1.sums.property] using hj)
  exact AspisR1EbyKPushDecodedProductUpdate.successful_push_decoded_product_update
    self value scalar out hcanonical hacc0 hacc1 hrun

#print axioms successful_push_product_update_of_count
end AspisR1DotProductCountBridgeV1
