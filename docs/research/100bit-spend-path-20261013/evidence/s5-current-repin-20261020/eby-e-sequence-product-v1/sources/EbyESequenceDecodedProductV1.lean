import AspisR1EbyEFourDotDecodedProductUpdateV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1EbyESequenceDecodedProductV1

open AspisR1EbyEFourDotDecodedProductUpdateV1
open AspisR1EbyEFourDotSourceStepV1
open AspisR1EbyEFourDotGeneratedPushPortV1
open AspisR1EbyEFourDotFromWideBridgeV1

abbrev State := AspisR1EbyEFourDotSourceStepV1.State
abbrev Wide := AspisR1EbyEFourDotSourceStepV1.Wide
abbrev Tower := AspisR1EbyEFourDotDecodedProductUpdateV1.WideTower

/-- Algebraic field-product sum for a finite sequence of EbyE operands. -/
def decodedProductSum : List (Wide × Wide) → Tower
  | [] => 0
  | (left,right)::tail =>
      sourceWideDecode left * sourceWideDecode right + decodedProductSum tail

/-- A format-independent trace certificate for a sequence of successful
emitted EbyE pushes. Each step carries precisely the invariants required by
the one-step theorem. This relation does not claim that an outer Rust loop
produces the trace. -/
inductive SuccessfulPushTrace : Nat → State → List (Wide × Wide) → State → Prop where
  | nil (n : Nat) (state : State) :
      SuccessfulPushTrace n state [] state
  | step {n : Nat} {state next final : State}
      {left right : Wide} {tail : List (Wide × Wide)} :
      Bounded n state →
      state.count.val = n →
      sourceCanonical left →
      sourceCanonical right →
      emittedPushParameterized
        AspisR1EbyEFourDotSourceStepV1.maxTerms
        AspisR1EbyEFourDotFromWideBridgeV1.sourceFromWide
        (AspisR1EbyEFourDotSourceStepV1.dotViaRawSource
          AspisR1EbyKPushActualRawCoefficientBounds.QRaw)
        AspisR1EbyEFourDotSourceStepV1.sourceAddUsize state left right =
          .ok (.Ok (), next) →
      SuccessfulPushTrace (n + 1) next tail final →
      SuccessfulPushTrace n state ((left,right)::tail) final

theorem successful_trace_decoded_product_sum
    {n : Nat} {initial final : State} {items : List (Wide × Wide)}
    (htrace : SuccessfulPushTrace n initial items final) :
    decodeState final = decodeState initial + decodedProductSum items := by
  induction htrace with
  | nil n state => simp [decodedProductSum]
  | @step n state next final left right tail hinv hcount hleft hright hpush htail ih =>
      have hstep := emitted_push_decoded_product_update n state next left right
        hinv hcount hleft hright hpush
      rw [ih, hstep]
      simp [decodedProductSum, add_assoc]

#print axioms successful_trace_decoded_product_sum

end AspisR1EbyESequenceDecodedProductV1
