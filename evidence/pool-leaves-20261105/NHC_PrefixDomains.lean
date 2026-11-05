import NHC_NGG_DecodePrefix
import NHC_NGG_RequestLength
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace NHC_PrefixDomains
open NHC_NGG_SpineRef NHC_NGG_DecodePrefix
/-- An accepted model prefix forces availability of the same three account
positions. Arbitrary extra accounts are retained; no count-3 fixture premise. -/
theorem account_window {R : Type} (reply : core.result.Result R NGGSpineError)
    (count : Usize) (hints : Hints) (value : R × Array Usize 3#usize × Hints)
    (accepted : finish reply count hints = .Ok value) : 3 ≤ count.val := by
  cases reply with
  | Err e => simp [finish] at accepted
  | Ok r =>
    by_cases h0 : count = 0#usize
    · simp [finish,h0] at accepted
    · by_cases h2 : count < 2#usize
      · simp [finish,h0,h2] at accepted
      · by_cases h3 : count < 3#usize
        · simp [finish,h0,h2,h3] at accepted
        · change ¬ count.val < 3 at h3
          omega
#print axioms account_window

theorem positions {R : Type} (reply : core.result.Result R NGGSpineError)
    (count : Usize) (hints : Hints) (value : R × Array Usize 3#usize × Hints)
    (accepted : finish reply count hints = .Ok value) :
    0 < count.val ∧ 1 < count.val ∧ 2 < count.val := by
  have bound := account_window reply count hints value accepted
  omega
#print axioms positions

/-- Decoder errors precede all three account reads in the emitted model. -/
theorem error_first {R : Type} (e : NGGSpineError) (count : Usize) (hints : Hints) :
    resume (.Err e : core.result.Result R NGGSpineError) count hints = ok (.Err e) := by
  rw [resume_eq]
  rfl
#print axioms error_first

/-- Existing installed request-decoder law derives the accepted instruction
length; this is independent of any native fixed-length observation. -/
theorem production_length (whole body : Slice U8)
    (request : AspisR1.NFY_JHd_RequestNative.Request)
    (atLeastFour : 4 ≤ whole.val.length)
    (window : body.val = whole.val.take (whole.val.length-4))
    (accepted : AspisR1.NFY_JHd_RequestNative.decode body = ok (.Ok request)) :
    whole.val.length = 324 :=
  NHC_NGG_RequestLength.payload whole body request atLeastFour window accepted
#print axioms production_length
end NHC_PrefixDomains
