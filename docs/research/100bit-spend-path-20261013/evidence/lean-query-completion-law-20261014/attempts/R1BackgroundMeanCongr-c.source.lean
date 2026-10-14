import R0C.V3.BSOk

/-! Congruence of background means from equality on lists of sampled length. -/
set_option autoImplicit false
namespace AspisR1.BackgroundMean

open R0C.V3

theorem pmean_congr_length {I A : Type} [Fintype A]
    (pre : List (I × Option A)) (f g : List A → ℚ)
    (h : ∀ as, as.length = pre.length → f as = g as) :
    R0C.V3.pmean f pre = R0C.V3.pmean g pre := by
  induction pre generalizing f g with
  | nil => exact h [] rfl
  | cons entry rest ih =>
      rcases entry with ⟨i, value⟩
      cases value with
      | some b =>
          change R0C.V3.pmean (fun as => f (b :: as)) rest =
            R0C.V3.pmean (fun as => g (b :: as)) rest
          apply ih
          intro as hlen
          apply h (b :: as)
          simpa using hlen
      | none =>
          change R0Z.mean (fun a => R0C.V3.pmean (fun as => f (a :: as)) rest) =
            R0Z.mean (fun a => R0C.V3.pmean (fun as => g (a :: as)) rest)
          apply congrArg R0Z.mean
          funext a
          apply ih
          intro as hlen
          apply h (a :: as)
          simpa using hlen

#print axioms pmean_congr_length

end AspisR1.BackgroundMean
