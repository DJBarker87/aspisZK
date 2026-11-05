import NFD_RequestDomains
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace NGG_RequestLength
/-- The installed decoder's success fixes the SAME input length. -/
theorem decoder (bytes : Slice U8) (request : AspisR1.JHd_RequestNative.Request)
    (accepted : AspisR1.JHd_RequestNative.decode bytes = ok (.Ok request)) :
    bytes.val.length = 320 := by
  by_contra bad
  have wrong := NFD_RequestDomains.wrong_length bytes bad
  change AspisR1.JHd_RequestNative.decode bytes = _ at wrong
  rw [accepted] at wrong
  cases wrong
#print axioms decoder

/-- No bound on the original payload is assumed: accepted decode plus the
actual strip window derives the324-byte accepted class. -/
theorem payload (whole body : Slice U8) (request : AspisR1.JHd_RequestNative.Request)
    (atLeastFour : 4 ≤ whole.val.length)
    (window : body.val = whole.val.take (whole.val.length-4))
    (accepted : AspisR1.JHd_RequestNative.decode body = ok (.Ok request)) :
    whole.val.length = 324 := by
  have width := decoder body request accepted
  rw [window,List.length_take] at width
  have h : whole.val.length-4 ≤ whole.val.length := by omega
  rw [Nat.min_eq_left h] at width
  omega
#print axioms payload
end NGG_RequestLength
