import R1Z.PV_RunJoin_CommonObserver32
set_option autoImplicit false
namespace R1Z.PV_RJDec_TotalExtension
open Aeneas Aeneas.Std Result ProverCommitSemanticTransport26
variable {A B V : Type}
/-- Exact all-Result extension obligation for fixed decoders. The failure and
 divergence clauses include unreachable Results as Common requires. -/
theorem cases_iff (project : A → B) (left : Result A → V) (right : Result B → V) :
    (∀ out, left out = right (mapR project out)) ↔
    (∀ a, left (.ok a) = right (.ok (project a))) ∧
    (∀ e, left (.fail e) = right (.fail e)) ∧
    left .div = right .div := by
  constructor
  · intro law
    exact ⟨fun a => law (.ok a), fun e => law (.fail e), law .div⟩
  · rintro ⟨success,failure,divergence⟩ out
    cases out with
    | ok a => exact success a
    | fail e => exact failure e
    | div => exact divergence
/-- Reachable-run laws do not constrain the fixed extension at any absent
Result. This isolates the extra obligation without changing an observer. -/
theorem unreachable_free (reachable : Result A → Prop)
    (left right : Result A → V) (absent : Result A)
    (not_reachable : ¬ reachable absent)
    (same : ∀ out, out ≠ absent → left out = right out) :
    ∀ out, reachable out → left out = right out := by
  intro out admitted
  apply same out
  intro eq
  exact not_reachable (eq ▸ admitted)
#print axioms cases_iff
#print axioms unreachable_free
end R1Z.PV_RJDec_TotalExtension
