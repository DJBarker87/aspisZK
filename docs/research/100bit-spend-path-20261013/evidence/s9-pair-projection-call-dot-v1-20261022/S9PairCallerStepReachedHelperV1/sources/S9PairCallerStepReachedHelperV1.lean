import AspisR1S9PairCallerStepV1.Funs

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9PairCallerStepReachedHelperV1

open AspisR1S9PairCallerStepV1

/-- The emitted discriminant comparison selects the S2 branch for the actual
S2 constructor. -/
theorem variant_s2_eq_true :
    transport.Variant.Insts.CoreCmpPartialEqVariant.eq
      transport.Variant.S2 transport.Variant.S2 = .ok true := by
  unfold transport.Variant.Insts.CoreCmpPartialEqVariant.eq
  simp [transport.Variant.read_discriminant]

/-- In the S2 specialization, successful execution of the emitted projection
caller retains the exact helper result and the exact subsequent four-slot
projection-loop result. The panic fallback is unreachable because the emitted
variant comparison is true. -/
theorem s2_projection_success_reaches_helper_and_loop
    (w : weights.Weights) (f : Slice U8)
    (ap0 ap1 : Array field.WideExact (4#usize))
    (low : Array field.WideExact (16#usize))
    (parts out : Array field.WideExact (7#usize))
    (hvariant : w.variant = transport.Variant.S2)
    (hprojection : weights.Weights.pair_s2_libra_parts_projection
      w f ap0 ap1 low parts = .ok out) :
    ∃ libra : Array field.WideExact (4#usize),
      weights.factored_s2_libra_weights ap0 ap1 w.extra = .ok libra ∧
      weights.Weights.pair_s2_libra_parts_projection_loop
        { start := 0#usize, «end» := 4#usize } f parts libra = .ok out := by
  unfold weights.Weights.pair_s2_libra_parts_projection at hprojection
  rw [hvariant] at hprojection
  simp only [variant_s2_eq_true, bind_tc_ok, if_pos] at hprojection
  cases hhelper : weights.factored_s2_libra_weights ap0 ap1 w.extra with
  | ok libra =>
      simp only [hhelper, bind_tc_ok] at hprojection
      exact ⟨libra, rfl, hprojection⟩
  | fail e =>
      simp only [hhelper, bind_tc_fail] at hprojection
      cases hprojection
  | div =>
      simp only [hhelper, bind_tc_div] at hprojection
      cases hprojection

#print axioms variant_s2_eq_true
#print axioms s2_projection_success_reaches_helper_and_loop

end AspisR1S9PairCallerStepReachedHelperV1
