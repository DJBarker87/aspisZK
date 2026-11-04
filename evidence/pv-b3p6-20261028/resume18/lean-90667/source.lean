import PV_B3P_DominatedEvents578227
namespace PV_B3P_TableEvents592227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_InitializerEvents578227
set_option autoImplicit false
/-- Two successful reads from a complete immutable scalar table projection.
Native initialization and reference reads consume the shared owner relation. -/
def sourceEvent (bound : Nat) (table : List (List (Fin bound)))
    (row column : Nat) (effects : List (Result Unit)) : Result (Option IndexState) :=
  match table[row]? with
  | none => .ok none
  | some fields =>
    match fields[column]? with
    | none => .ok none
    | some value => through effects (some ⟨value.val,bound⟩)

theorem event_certificate {α : Type} (bound : Nat) (table : List (List (Fin bound)))
    (row column : Nat) (effects : List (Result Unit)) (observed : IndexState)
    (ran : sourceEvent bound table row column effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second := by
  apply (index_out_of_bounds observed normal first second).2
  cases found : table[row]? with
  | none => simp only [sourceEvent,found] at ran; cases ran
  | some fields =>
    cases field : fields[column]? with
    | none => simp only [sourceEvent,found,field] at ran; cases ran
    | some value =>
      simp only [sourceEvent,found,field] at ran
      have frame := through_value _ _ _ ran
      cases frame
      exact value.isLt
#print axioms event_certificate
end PV_B3P_TableEvents592227
