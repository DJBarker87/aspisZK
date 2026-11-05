import NIL_FreshOps
set_option autoImplicit false
noncomputable section
namespace NIL_TryTransport
open Aeneas Aeneas.Std Result NIL_Carriers

def fresh {A B : Type} (r : core.result.Result A Fresh.Err)
 (next : A → Result (core.result.Result B Fresh.Err)) : Result (core.result.Result B Fresh.Err) := do
 let cf ← core.result.Result.Insts.CoreOpsTry.branch r
 match cf with
 | .Continue x => next x
 | .Break err => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual B (core.convert.FromSame Fresh.Err) err

def cohort {A B : Type} (r : core.result.Result A Cohort.Err)
 (next : A → Result (core.result.Result B Cohort.Err)) : Result (core.result.Result B Cohort.Err) := do
 let cf ← core.result.Result.Insts.CoreOpsTry.branch r
 match cf with
 | .Continue x => next x
 | .Break err => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual B (core.convert.FromSame Cohort.Err) err

theorem map_try {A B C D : Type} (g : A → B) (f : C → D)
 (r : core.result.Result A Cohort.Err) (next : B → Result (core.result.Result C Fresh.Err)) :
 outer (NIL_Carriers.inner f) (fresh (unInner g r) next)=
 cohort r (fun x=>outer (NIL_Carriers.inner f) (next (g x))) := by
 cases r with
 | Ok x => rfl
 | Err err =>
   change (ok (.Err (error (unError err))) : Result (core.result.Result D Cohort.Err))=ok (.Err err)
   rw [error_reverse]

theorem fresh_err {A B : Type} (err : Fresh.Err)
 (next : A → Result (core.result.Result B Fresh.Err)) : fresh (.Err err) next=ok (.Err err) := rfl

theorem fresh_ok {A B : Type} (x : A)
 (next : A → Result (core.result.Result B Fresh.Err)) : fresh (.Ok x) next=next x := rfl
#print axioms map_try
#print axioms fresh_err
#print axioms fresh_ok
end NIL_TryTransport
