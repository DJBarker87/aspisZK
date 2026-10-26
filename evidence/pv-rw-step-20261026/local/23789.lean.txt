import R1Z.PV_RW_ResultListRun
set_option autoImplicit false
namespace R1Z.PV_RW_ResultListTotal
open Aeneas Aeneas.Std Result

theorem total {T S : Type} (step : T → S → Result S)
    (each : ∀ value state, ∃ next, step value state=ok next)
    (values : List T) (state : S) : ∃ final, PV_RW_ResultListRun.run step values state=ok final := by
  induction values generalizing state with
  | nil => exact ⟨state,rfl⟩
  | cons value tail ih =>
    obtain ⟨next,hn⟩ := each value state
    obtain ⟨final,hf⟩ := ih next
    refine ⟨final,?_⟩
    simp only [PV_RW_ResultListRun.run,hn,bind_tc_ok]
    exact hf

theorem append {T S : Type} (step : T → S → Result S) (left right : List T) (state : S) :
    PV_RW_ResultListRun.run step (left++right) state=(do
      let middle ← PV_RW_ResultListRun.run step left state
      PV_RW_ResultListRun.run step right middle) := by
  induction left generalizing state with
  | nil => rfl
  | cons value tail ih =>
    simp only [List.cons_append,PV_RW_ResultListRun.run,bind_assoc_eq]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro next _
    exact ih next
#print axioms total
#print axioms append
end R1Z.PV_RW_ResultListTotal
