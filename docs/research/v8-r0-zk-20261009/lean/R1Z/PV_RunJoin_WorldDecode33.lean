import R1Z.PV_W_SourceSyntax
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WorldDecode33
open PV_W_Threading
variable {W C A View : Type}

/-- The old Result-only interface retains post-world on returned values but
forgets it on source failure/divergence. Its adequacy must be proved. -/
def returned (r : Run W C Aeneas.Std.Error A) : Aeneas.Std.Result (A × W) :=
  match r.outcome with
  | .ok a => .ok (a,r.world)
  | .fail e => .fail e
  | .div => .div

/-- Necessary for each complete disclosed/oracle decoder separately. No
native trace, error payload or failure event is weakened by this statement. -/
theorem same_result (decode : Aeneas.Std.Result (A × W) → View)
    (observe : Run W C Aeneas.Std.Error A → View)
    (law : ∀ r, decode (returned r) = observe r)
    (left right : Run W C Aeneas.Std.Error A) (same : returned left = returned right) :
    observe left = observe right := by
  rw [← law left,← law right,same]

theorem source_failure (decode : Aeneas.Std.Result (A × W) → View)
    (observe : Run W C Aeneas.Std.Error A → View)
    (law : ∀ r, decode (returned r) = observe r)
    (left right : Run W C Aeneas.Std.Error A) (e : Aeneas.Std.Error)
    (hl : left.outcome = .fail e) (hr : right.outcome = .fail e) :
    observe left = observe right := by
  apply same_result decode observe law left right
  simp only [returned,hl,hr]

theorem source_divergence (decode : Aeneas.Std.Result (A × W) → View)
    (observe : Run W C Aeneas.Std.Error A → View)
    (law : ∀ r, decode (returned r) = observe r)
    (left right : Run W C Aeneas.Std.Error A)
    (hl : left.outcome = .div) (hr : right.outcome = .div) :
    observe left = observe right := by
  apply same_result decode observe law left right
  simp only [returned,hl,hr]

/-- A Result-only decoder cannot be supplied if one fixed interpreted body
has same-result runs with different complete observations. This is a
conditional obstruction, not a checked counterexample to deployed code. -/
theorem no_decoder (observe : Run W C Aeneas.Std.Error A → View)
    (left right : Run W C Aeneas.Std.Error A) (same : returned left = returned right)
    (different : observe left ≠ observe right) :
    ¬ ∃ decode : Aeneas.Std.Result (A × W) → View, ∀ r, decode (returned r) = observe r := by
  intro ⟨decode,law⟩
  exact different (same_result decode observe law left right same)

#print axioms same_result
#print axioms source_failure
#print axioms source_divergence
#print axioms no_decoder
end R1Z.PV_RunJoin_WorldDecode33
