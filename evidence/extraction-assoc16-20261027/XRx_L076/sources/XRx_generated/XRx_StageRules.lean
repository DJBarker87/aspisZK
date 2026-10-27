import XRx_StageFold
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRx_StageRules
open XRx_StageFold
/-- An error stops stage calls immediately, for every remaining length. -/
theorem stopped {E S : Type} (step : Nat → S → Result (core.result.Result S E))
 (n i : Nat) (e : E) : unrolled step i n (.Err e)=ok (.Err e) := by
 induction n generalizing i with
 | zero => rfl
 | succ n ih => simp only [unrolled,advance,bind_tc_ok,ih]

def chain {E S O : Type} (r : Result (core.result.Result S E))
 (k : S → Result (core.result.Result O E)) : Result (core.result.Result O E) := do
 let next ← r
 match next with | .Err e => ok (.Err e) | .Ok s => k s

/-- A single symbolic first-stop stage, without hand-unrolling any driver. -/
theorem next {E S : Type} (step : Nat → S → Result (core.result.Result S E))
 (n i : Nat) (s : S) : unrolled step i (n+1) (.Ok s)=
 chain (step i s) (fun out => unrolled step (i+1) n (.Ok out)) := by
 simp only [unrolled,advance,chain]
 congr 1
 funext out
 cases out with
 | Err e => exact stopped step n (i+1) e
 | Ok x => rfl

/-- Generic stage association composes without changing state or error
carriers; it includes both outer failures and all inner errors. -/
theorem stages {E S : Type}
 (left right : Nat → S → Result (core.result.Result S E))
 (equal : ∀ i s, left i s=right i s)
 (n i : Nat) (s : core.result.Result S E) :
 unrolled left i n s=fold right (List.range' i n) s := by
 have same : left=right := funext (fun i => funext (equal i))
 subst right
 exact source left n i s
#print axioms stopped
#print axioms next
#print axioms stages
end XRx_StageRules
