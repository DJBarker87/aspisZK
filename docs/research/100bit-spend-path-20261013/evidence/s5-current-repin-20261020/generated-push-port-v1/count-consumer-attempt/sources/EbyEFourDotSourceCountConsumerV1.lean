import AspisR1EbyEFourDotSourceStepV1
import AspisR1EbyEFourDotFromWideBridgeV1
import AspisR1EbyEFourDotGeneratedPushPortV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1EbyEFourDotSourceCountConsumerV1

open AspisR1EbyEFourDotSourceStepV1
open AspisR1EbyEFourDotFromWideBridgeV1
open AspisR1EbyEFourDotGeneratedPushPortV1

theorem emitted_push_success_count_bound
    (rawFn : RawFn) (n : Nat) (self out : State)
    (left right : Wide)
    (hinv : Bounded n self)
    (hcount : self.count.val = n)
    (h : emittedPushParameterized maxTerms sourceFromWide
      (dotViaRawSource rawFn) sourceAddUsize self left right =
        .ok (.Ok (), out)) :
    Bounded (n + 1) out ∧
      (∀ j, ∀ hj : j < 4,
        (self.ac.sums.val[j]'(by rw [self.ac.sums.property]; exact hj)).val < 2^46) ∧
      (∀ j, ∀ hj : j < 4,
        (self.bd.sums.val[j]'(by rw [self.bd.sums.property]; exact hj)).val < 2^46) ∧
      (∀ j, ∀ hj : j < 4,
        (self.ad.sums.val[j]'(by rw [self.ad.sums.property]; exact hj)).val < 2^46) ∧
      (∀ j, ∀ hj : j < 4,
        (self.bc.sums.val[j]'(by rw [self.bc.sums.property]; exact hj)).val < 2^46) := by
  apply successful_four_dot_count_bound sourceFromWide rawFn n self out left right hinv hcount
  rw [emittedPushParameterized_eq_sourceSchedule] at h
  exact h

#print axioms emitted_push_success_count_bound

end AspisR1EbyEFourDotSourceCountConsumerV1
