import NIL_StatePort
set_option autoImplicit false
noncomputable section
namespace NIL_ReplyCases
open Aeneas Aeneas.Std Result NIL_Carriers NIL_StatePort

theorem ok_iff (r : Result (core.result.Result (F.P × F.A) Fresh.Err)) (p : F.P) (a : F.A) :
 reply r=ok (.Ok (prepared p,accumulator a)) ↔ r=ok (.Ok (p,a)) := by
 constructor
 · intro h
   apply reply_injective
   exact h
 · intro h;rw [h];rfl

theorem err_iff (r : Result (core.result.Result (F.P × F.A) Fresh.Err)) (err : Fresh.Err) :
 reply r=ok (.Err (error err)) ↔ r=ok (.Err err) := by
 constructor
 · intro h;apply reply_injective;exact h
 · intro h;rw [h];rfl

theorem fail_iff (r : Result (core.result.Result (F.P × F.A) Fresh.Err)) (err : Aeneas.Std.Error) :
 reply r=fail err ↔ r=fail err := by
 constructor
 · intro h;apply reply_injective;exact h
 · intro h;rw [h];rfl

theorem div_iff (r : Result (core.result.Result (F.P × F.A) Fresh.Err)) :
 reply r=div ↔ r=div := by
 constructor
 · intro h;apply reply_injective;exact h
 · intro h;rw [h];rfl
#print axioms ok_iff
#print axioms err_iff
#print axioms fail_iff
#print axioms div_iff
end NIL_ReplyCases
