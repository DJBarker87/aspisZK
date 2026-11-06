import NLA_RootPrefix
set_option autoImplicit false
noncomputable section
namespace NLA_DataPrefix
open Aeneas Aeneas.Std Result
abbrev PE := NKF_BoxModel.PE
/-- Ordered data acquisition followed by exactly one decoder at its returned
slice. The bytes are unrestricted; no fixed allocation length enters G. -/
def decode {A E : Type} (data : Result (core.result.Result (Slice U8) PE))
 (decoder : Slice U8 → Result (core.result.Result A E)) :
 Result (core.result.Result A PE) := do
 let r ← data
 match r with
 | .Err e => ok (.Err e)
 | .Ok bytes => NKF_BoxModel.outer (decoder bytes)

theorem error {A E : Type} (e : PE)
 (decoder : Slice U8 → Result (core.result.Result A E)) :
 decode (ok (.Err e)) decoder = ok (.Err e) := rfl

theorem success {A E : Type} (bytes : Slice U8)
 (decoder : Slice U8 → Result (core.result.Result A E)) :
 decode (ok (.Ok bytes)) decoder = NKF_BoxModel.outer (decoder bytes) := rfl

theorem mapped_error {A E : Type} (bytes : Slice U8) (e : E) :
 decode (ok (.Ok bytes)) (fun _ => (ok (.Err e) : Result (core.result.Result A E))) =
 ok (.Err PE.InvalidAccountData) := rfl

theorem abort {A E : Type} (e : Error)
 (decoder : Slice U8 → Result (core.result.Result A E)) :
 decode (.fail e) decoder = .fail e := rfl

theorem divergence {A E : Type}
 (decoder : Slice U8 → Result (core.result.Result A E)) :
 decode .div decoder = .div := rfl

/-- Explicit byte-parametricity: after acquisition the full decoder Result
at exactly these bytes determines G, for arbitrary length and all errors.
It is algebraic support; native input/frame association is still required. -/
theorem reply_parametric {A E : Type} (bytes₁ bytes₂ : Slice U8)
 (decoder : Slice U8 → Result (core.result.Result A E))
 (same : decoder bytes₁ = decoder bytes₂) :
 decode (ok (.Ok bytes₁)) decoder = decode (ok (.Ok bytes₂)) decoder := by
 simp only [success,same]

#print axioms error
#print axioms success
#print axioms mapped_error
#print axioms abort
#print axioms divergence
#print axioms reply_parametric
end NLA_DataPrefix
