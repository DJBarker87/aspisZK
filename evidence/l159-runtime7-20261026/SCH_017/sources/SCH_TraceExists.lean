import GExq_Caller
set_option autoImplicit false
namespace AspisR1.SCH_TraceExists
open Aeneas Aeneas.Std Result S2W_Trace

/-- Reify the successful trace from the execution itself. No independently
chosen successful event list is an input. -/
theorem accepted {A : Type} (ops : AdapterRw.Ops) (code : Code A)
    (value : A) (before : Log) (success : erase ops code = ok value) :
    ∃ after, run ops code before = ok (value,after) := by
  induction code generalizing before with
  | done a => cases Result.ok.inj success; exact ⟨before,rfl⟩
  | step r k ih =>
    cases r with
    | fail e => cases success
    | div => cases success
    | ok a => exact ih a before success
  | call op k ih =>
    cases h : invoke ops op with
    | fail e => simp only [erase,h,bind_tc_fail] at success; cases success
    | div => simp only [erase,h,bind_tc_div] at success; cases success
    | ok a =>
      simp only [erase,h,bind_tc_ok] at success
      obtain ⟨after,ran⟩ := ih a (before ++ [.returned op a]) success
      exact ⟨after,by simpa only [run,h,thenResult] using ran⟩

#print axioms accepted
end AspisR1.SCH_TraceExists
