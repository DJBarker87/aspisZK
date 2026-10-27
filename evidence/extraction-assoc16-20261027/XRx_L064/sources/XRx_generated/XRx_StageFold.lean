import XRn_Join_Funs
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRx_StageFold
/-- Execute one stage only while the preceding state is successful. Both
outer failure/divergence and the arbitrary inner error are preserved. -/
def advance {E S : Type} (step : Nat → S → Result (core.result.Result S E))
 (i : Nat) (state : core.result.Result S E) : Result (core.result.Result S E) :=
 match state with
 | .Err e => ok (.Err e)
 | .Ok s => step i s

def unrolled {E S : Type} (step : Nat → S → Result (core.result.Result S E)) :
 Nat → Nat → core.result.Result S E → Result (core.result.Result S E)
 | _,0,s => ok s
 | i,n+1,s => do
   let next ← advance step i s
   unrolled step (i+1) n next

def fold {E S : Type} (step : Nat → S → Result (core.result.Result S E)) :
 List Nat → core.result.Result S E → Result (core.result.Result S E)
 | [],s => ok s
 | i::is,s => do
   let next ← advance step i s
   fold step is next

/-- One generic first-stop law, parametric in stage, error and state. -/
theorem source {E S : Type} (step : Nat → S → Result (core.result.Result S E))
 (n i : Nat) (s : core.result.Result S E) :
 unrolled step i n s = fold step (List.range' i n) s := by
 induction n generalizing i s with
 | zero => rfl
 | succ n ih =>
  simp only [unrolled,List.range'_succ,fold]
  congr 1
  funext next
  exact ih (i+1) next

/-- The SAME finish continuation runs exactly when all stages succeed. -/
theorem finish {E S O : Type}
 (step : Nat → S → Result (core.result.Result S E))
 (last : S → Result (core.result.Result O E)) (n i : Nat)
 (s : core.result.Result S E) :
 (do let out ← unrolled step i n s
     match out with | .Err e => ok (core.result.Result.Err e : core.result.Result O E) | .Ok x => last x) =
 (do let out ← fold step (List.range' i n) s
     match out with | .Err e => ok (core.result.Result.Err e : core.result.Result O E) | .Ok x => last x) := by
 rw [source]

#print axioms source
#print axioms finish
end XRx_StageFold
