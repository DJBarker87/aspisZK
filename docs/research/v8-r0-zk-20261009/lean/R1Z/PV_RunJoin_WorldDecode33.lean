import R1Z.PV_W_SourceSyntax
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WorldDecode33
open PV_W_Threading
variable {W C E A View : Type}

/-- The old Result-only interface retains post-world on returned values but
forgets it on source failure/divergence. Its adequacy must be proved. -/
def returned (r : Run W C E A) : Except E (Option (A × W)) :=
  match r.outcome with
  | .ok a => .ok (some (a,r.world))
  | .fail e => .error e
  | .div => .ok none

/-- Necessary for each complete disclosed/oracle decoder separately. No
native trace, error payload or failure event is weakened by this statement. -/
theorem same_result (decode : Except E (Option (A × W)) → View)
    (observe : Run W C E A → View)
    (law : ∀ r, decode (returned r) = observe r)
    (left right : Run W C E A) (same : returned left = returned right) :
    observe left = observe right := by
  rw [← law left,← law right,same]

theorem source_failure (decode : Except E (Option (A × W)) → View)
    (observe : Run W C E A → View)
    (law : ∀ r, decode (returned r) = observe r)
    (left right : Run W C E A) (e : E)
    (hl : left.outcome = .fail e) (hr : right.outcome = .fail e) :
    observe left = observe right := by
  apply same_result decode observe law left right
  simp only [returned,hl,hr]

theorem source_divergence (decode : Except E (Option (A × W)) → View)
    (observe : Run W C E A → View)
    (law : ∀ r, decode (returned r) = observe r)
    (left right : Run W C E A)
    (hl : left.outcome = .div) (hr : right.outcome = .div) :
    observe left = observe right := by
  apply same_result decode observe law left right
  simp only [returned,hl,hr]

/-- A Result-only decoder cannot be supplied if one fixed interpreted body
has same-result runs with different complete observations. This is a
conditional obstruction, not a checked counterexample to deployed code. -/
theorem no_decoder (observe : Run W C E A → View)
    (left right : Run W C E A) (same : returned left = returned right)
    (different : observe left ≠ observe right) :
    ¬ ∃ decode, ∀ r, decode (returned r) = observe r := by
  intro ⟨decode,law⟩
  exact different (same_result decode observe law left right same)

#print axioms same_result
#print axioms source_failure
#print axioms source_divergence
#print axioms no_decoder
end R1Z.PV_RunJoin_WorldDecode33
