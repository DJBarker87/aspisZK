import S9ActualEbyKBackendTransportV1
import S9ActualPairWideCanonicalV1
import EbyKPowerValueCanonicalToPushV5
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9NativeWidePushCanonicalV1
open AspisR1S9ActualEbyKBackendTransportV1
abbrev W := AspisR1S9ProductionPairCutV1.aspis_core.field.wide_exact.WideExact

/-- The exact existing push/minimal-field map and native/current-field map
copy the same eight coordinates. No raw arithmetic is involved. -/
theorem native_push_current_coordinates (w : W) :
    AspisR1EbyKPowerValueCanonicalToPush.pushToSource (toSourceWide w)=
      AspisR1CurrentWide.Proof.toMinimalWide
        (AspisR1S9ActualPairWideCanonicalV1.toCurrent w) := by rfl

theorem native_canonical_push (w : W)
    (h : AspisR1S9ActualPairWideCanonicalV1.Canonical w) :
    AspisR1EbyKPowerValueCanonicalToPush.pushCanonical (toSourceWide w) := by
  change AspisR1CurrentWideMul.CanonicalWide
    (AspisR1EbyKPowerValueCanonicalToPush.pushToSource (toSourceWide w))
  rw [native_push_current_coordinates]
  exact h

/-- Existing canonical-input raw coefficient bounds apply to the SAME native
words, without assuming source Q.raw correctness. This is operand-domain
information only; the opaque actual Rust raw refinement is still separate. -/
theorem native_canonical_eight_bounds (w : W)
    (h : AspisR1S9ActualPairWideCanonicalV1.Canonical w) :
    w.c0.c0.a.val ≤ 2^31-2 ∧ w.c0.c0.b.val ≤ 2^31-2 ∧
    w.c0.c1.a.val ≤ 2^31-2 ∧ w.c0.c1.b.val ≤ 2^31-2 ∧
    w.c1.c0.a.val ≤ 2^31-2 ∧ w.c1.c0.b.val ≤ 2^31-2 ∧
    w.c1.c1.a.val ≤ 2^31-2 ∧ w.c1.c1.b.val ≤ 2^31-2 := by
  exact AspisR1EbyKPowerValueCanonicalToPush.canonical_push_limb_bounds
    (toSourceWide w) (native_canonical_push w h)

#print axioms native_push_current_coordinates
#print axioms native_canonical_push
#print axioms native_canonical_eight_bounds
end AspisR1S9NativeWidePushCanonicalV1
