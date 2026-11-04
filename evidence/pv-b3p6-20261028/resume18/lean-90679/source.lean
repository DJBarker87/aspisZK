import PV_B3P_RangeComputedEvents592227
import PV_B3P_CopyBasicsSuccess227
namespace PV_B3P_RowEvents592227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_InitializerEvents578227
set_option autoImplicit false
def rowScalar (value : Nat) (small : value < 1024) : Usize :=
  Usize.ofNatCore value (by
    have max := Usize.cMax_bound_concrete.1
    scalar_tac)

/-- Consume a successful caller scalar observation. The observed length bound
is proved from all caller expressions or literal-table fields by the generator.
No arbitrary row-domain hypothesis appears at the deployed wrapper. -/
def sourceEvent (input : Result (Option IndexState)) (effects : List (Result Unit)) :
    Result (Option IndexState) := do
  let state ← input
  match state with
  | none => .ok none
  | some row =>
    (if small : row.index < 1024 then
      through effects (some ⟨(Usize.wrapping_shr (rowScalar row.index small) 4#u32).val,64⟩)
    else .ok none)

theorem event_certificate {α : Type} (input : Result (Option IndexState))
    (effects : List (Result Unit)) (observed : IndexState)
    (ran : sourceEvent input effects = .ok (some observed)) (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second := by
  apply (index_out_of_bounds observed normal first second).2
  cases input with
  | fail error => cases ran
  | div => cases ran
  | ok state =>
    cases state with
    | none => cases ran
    | some row =>
      simp only [sourceEvent,bind_tc_ok] at ran
      split at ran
      · rename_i small
        have frame := through_value _ _ _ ran
        cases frame
        exact PV_B3P_Success227.row_high (rowScalar row.index small) small
      · cases ran
#print axioms event_certificate
end PV_B3P_RowEvents592227
