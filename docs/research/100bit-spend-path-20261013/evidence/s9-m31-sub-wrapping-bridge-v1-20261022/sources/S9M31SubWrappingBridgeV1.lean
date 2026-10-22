import R22CanonicalM31AddSub
import CurrentWideBaseBridge
import ExtractedCurrentM31AddSub

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9M31SubWrappingBridgeV1

abbrev M := AspisR1Qm31ArithmeticProbe.field.M31
abbrev P : Nat := AspisR1.ExtractedCurrentM31AddSub.P

/-- Canonical-input bridge for the non-audit `field.rs` M31::sub expression
pinned at field.rs:94-119 (SHA 28df5a1abee13bde4b3aa9eeceb0489bedf00531f298460954a97661f5f1baea).
`wrappingSub` is the literal wrapping-scalar model of its `self + P - rhs`,
then conditional subtraction body. This states a mathematical wrapper result;
it does not claim a new source extraction or whole-caller refinement. -/
theorem wrapping_m31_sub_matches_checked
    (x y : M) (hx : x.val < P) (hy : y.val < P) :
    (AspisR1.R22CanonicalM31AddSub.wrappingSub x y).val < P ∧
    AspisR1Qm31ArithmeticProbe.field.M31.sub x y =
      .ok (AspisR1.R22CanonicalM31AddSub.wrappingSub x y) ∧
    AspisR1CurrentWide.field.M31.sub x y =
      .ok (AspisR1.R22CanonicalM31AddSub.wrappingSub x y) := by
  obtain ⟨z, hsub, _hvalue, hcanonical⟩ :=
    AspisR1.ExtractedCurrentM31AddSub.current_sub_mod x y hx hy
  have hwrap : AspisR1.R22CanonicalM31AddSub.wrappingSub x y = z := by
    apply Result.ok.inj
    exact (AspisR1.R22CanonicalM31AddSub.canonical_sub_agrees x y hx hy).symm.trans hsub
  have hsource : AspisR1Qm31ArithmeticProbe.field.M31.sub x y =
      .ok (AspisR1.R22CanonicalM31AddSub.wrappingSub x y) :=
    AspisR1.R22CanonicalM31AddSub.canonical_sub_agrees x y hx hy
  have hcurrent : AspisR1CurrentWide.field.M31.sub x y =
      .ok (AspisR1.R22CanonicalM31AddSub.wrappingSub x y) := by
    rw [AspisR1CurrentWide.Proof.m31_sub_same]
    exact hsource
  exact ⟨by rw [hwrap]; exact hcanonical, hsource, hcurrent⟩

#print axioms wrapping_m31_sub_matches_checked

end AspisR1S9M31SubWrappingBridgeV1
