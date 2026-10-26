import BEg_Observation
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEg_Continuation
open Aeneas Aeneas.Std Result SdkC_Source
open BEg_Observation

def bindResult {S A B E F : Type} (call : Parts → S → Result Digest × S)
    (k : A → Code (core.result.Result B F))
    (out : Result (core.result.Result A E) × S × Log) :
    Option B × S × Log :=
  match accepted out.1 with
  | some a => observe (BEf_Carrier.run call (k a) out.2.1 out.2.2)
  | none => (none,out.2)

/-- An error-insensitive continuation cannot observe the rejected error kind.
It sees the SAME successful output/carrier and therefore issues the SAME
adaptive suffix, or issues no suffix on rejection. -/
theorem transport {S A B E F G : Type} (call : Parts → S → Result Digest × S)
    (k : A → Code (core.result.Result B G))
    (left : Result (core.result.Result A E) × S × Log)
    (right : Result (core.result.Result A F) × S × Log)
    (same : observe left = observe right) :
    bindResult call k left = bindResult call k right := by
  have v := congrArg (fun out : Option A × S × Log => out.1) same
  have e := congrArg (fun out : Option A × S × Log => out.2) same
  change accepted left.1 = accepted right.1 at v
  change left.2 = right.2 at e
  unfold bindResult
  rw [v,e]

#print axioms transport
end AspisR1.BEg_Continuation
end
