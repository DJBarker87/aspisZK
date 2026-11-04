import NFG_QueryLoopDefs
import NFP_TraceTypes
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFS_LoopTraceDefs
open Aeneas Aeneas.Std Result AspisR1Stage2 NFP_TraceTypes NFG_QueryLoopDefs
def run (query : verifier.Accumulator → verifier.BatchedWeights → M State) (finish : Usize) : Nat → State → M State
 | 0,state => match state with
   | .Err _ => pure state
   | .Ok (a,_) => if a.next≥finish then pure state else eval div
 | fuel+1,state => match state with
   | .Err _ => pure state
   | .Ok (a,b) => if a.next≥finish then pure state else do
      let next ← query a b
      run query finish fuel next

theorem bind_congr {A B : Type} (before : M A) (first second : A → M B)
 (same : ∀ a,before.result=ok a → first a=second a) :
 (before >>= first)=(before >>= second) := by
 rcases before with ⟨r,cuts⟩
 cases r with
 | fail e => rfl
 | div => rfl
 | ok a => exact congrArg (fun after : M B=>NFI_TraceResult.M.mk after.result (cuts++after.cuts)) (same a rfl)

/-- Finite observation-preserving induction on an arbitrary prestate. -/
theorem compare (first second : A → B → M State) (valid : State → Prop)
 (finish : Usize)
 (same : ∀ a b,valid (.Ok (a,b)) → a.next.val<finish.val → first a b=second a b)
 (preserve : ∀ a b next,valid (.Ok (a,b)) → a.next.val<finish.val →
  (second a b).result=ok next → valid next)
 (fuel : Nat) (state : State) (input : valid state) :
 run first finish fuel state=run second finish fuel state := by
 induction fuel generalizing state with
 | zero => cases state with | Err e=>rfl | Ok pair=>cases pair;rfl
 | succ fuel ih =>
  cases state with
  | Err error => rfl
  | Ok pair =>
   rcases pair with ⟨a,b⟩
   by_cases stopped : a.next≥finish
   · simp only [run,stopped,if_true]
   · have inside : a.next.val<finish.val := Nat.lt_of_not_ge stopped
     simp only [run,stopped,if_false,same a b input inside]
     apply bind_congr
     intro next h
     exact ih next (preserve a b next input inside h)

theorem erased (query : A → B → M State) (finish : Usize) (fuel : Nat) (state : State) :
 (run query finish fuel state).result=NFG_QueryLoopDefs.run (fun a b=>(query a b).result) finish fuel state := by
 induction fuel generalizing state with
 | zero =>
  cases state with
  | Err e => rfl
  | Ok pair =>
   rcases pair with ⟨a,b⟩
   by_cases stopped : a.next≥finish <;>
    simp only [run,NFG_QueryLoopDefs.run,stopped,if_true,if_false,pure_result,eval,NFI_TraceResult.erase_lift]
 | succ fuel ih =>
  cases state with
  | Err error => rfl
  | Ok pair =>
   rcases pair with ⟨a,b⟩
   by_cases stopped : a.next≥finish
   · simp only [run,NFG_QueryLoopDefs.run,stopped,if_true,pure_result]
   · simp only [run,NFG_QueryLoopDefs.run,stopped,if_false,NFI_TraceResult.erase_bind,ih]
#print axioms bind_congr
#print axioms compare
#print axioms erased
end AspisR1.NFS_LoopTraceDefs
end
