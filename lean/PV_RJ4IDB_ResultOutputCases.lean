import PV_RJ4IDB_ResultOutput
set_option autoImplicit false
namespace PV_RJ4IDB
open Aeneas Aeneas.Std R1Z.ProverCommitRetry34
variable {P S T V O : Type}
/-- All three exact total-extension clauses for the proved returned-output
component. `disclose` and `observe` are unchanged component consumers; these
lemmas do not fix the missing native full-view/oracle decoders. -/
theorem output_disclosed_ok (s : S) (project : S → T)
 (v : Step (Published P)) (disclose : ReturnedOutput P → V) :
 disclose (resultOutput (.ok (v,s))) =
 disclose (resultOutput (.ok (v,project s))) := by
 cases v <;> rfl

theorem output_disclosed_fail (e : Error) (disclose : ReturnedOutput P → V) :
 disclose (resultOutput (S := S) (.fail e)) =
 disclose (resultOutput (S := T) (.fail e)) := rfl

theorem output_disclosed_div (disclose : ReturnedOutput P → V) :
 disclose (resultOutput (S := S) .div) =
 disclose (resultOutput (S := T) .div) := rfl

theorem output_oracle_ok (s : S) (project : S → T)
 (v : Step (Published P)) (observe : ReturnedOutput P → O) :
 observe (resultOutput (.ok (v,s))) =
 observe (resultOutput (.ok (v,project s))) := by
 cases v <;> rfl

theorem output_oracle_fail (e : Error) (observe : ReturnedOutput P → O) :
 observe (resultOutput (S := S) (.fail e)) =
 observe (resultOutput (S := T) (.fail e)) := rfl

theorem output_oracle_div (observe : ReturnedOutput P → O) :
 observe (resultOutput (S := S) .div) =
 observe (resultOutput (S := T) .div) := rfl
#print axioms output_disclosed_ok
#print axioms output_disclosed_fail
#print axioms output_disclosed_div
#print axioms output_oracle_ok
#print axioms output_oracle_fail
#print axioms output_oracle_div
end PV_RJ4IDB
