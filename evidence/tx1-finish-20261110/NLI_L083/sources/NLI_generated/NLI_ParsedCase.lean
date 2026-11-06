import NLI_RoundsCarry
set_option autoImplicit false
namespace AspisR1.NLI_ParsedCase
open Aeneas Aeneas.Std Result
/-- Eliminate a CLOSED packet's dependent parse match while retaining the
SAME parser equation. Rewriting the discriminant alone is ill-typed. -/
theorem success {A E : Type} (reply : Result (core.result.Result A E))
 (P : ∀ value,reply=ok (.Ok value) → Prop)
 (packet : match (generalizing := false) h:reply with | .ok (.Ok value)=>P value h | _=>True)
 (value : A) (parsed : reply=ok (.Ok value)) : P value parsed := by
 subst reply
 exact packet
#print axioms success
end AspisR1.NLI_ParsedCase
