import R0P.Poseidon
import Lean

set_option autoImplicit false
namespace NJE_PermutationFold
open Lean Elab Tactic

-- Reuse the existing checked private theorem, discovered in L044. The tactic
-- constructs only an application of that named theorem; the kernel checks it.
-- No duplicate schedule proof and no new axiom or runtime assumption.
theorem folded {K : Type} [Field K] (state : Fin 16 → K) :
    (List.ofFn (fun r : Fin 22 => r)).foldl (fun s r => R0P.poseidonApplyRound r s)
      (R0P.poseidonExternalLinear state)=R0P.poseidonPermutation state := by
 change (List.ofFn (fun r : Fin 22 => r)).foldl (fun s r => R0P.poseidonApplyRound r s)
   (R0P.poseidonExternalLinear state)=_
 unfold R0P.poseidonPermutation
 run_tac do
   let n := Name.str (Name.str (Name.num `_private.R0P.Poseidon 0) "R0P") "poseidon_rounds_split"
   let original ← Lean.Elab.Term.elabTerm (mkIdent `state) none
   let s ← Lean.Meta.mkAppM ``R0P.poseidonExternalLinear #[original]
   let proof ← Lean.Meta.mkAppM n #[s]
   (← getMainGoal).assign proof
   replaceMainGoal []

theorem compose {σ : Type} {n : Nat} (states : Fin (n+1) → σ)
    (steps : Fin n → σ → σ)
    (next : ∀ i, states i.succ=steps i (states i.castSucc)) :
    (List.ofFn steps).foldl (fun s step => step s) (states 0)=states (Fin.last n) := by
 run_tac do
   let name := Name.str (Name.str (Name.num `_private.R0P.Poseidon 0) "R0P") "poseidon_compose_steps"
   let a ← Lean.Elab.Term.elabTerm (mkIdent `states) none
   let b ← Lean.Elab.Term.elabTerm (mkIdent `steps) none
   let c ← Lean.Elab.Term.elabTerm (mkIdent `next) none
   (← getMainGoal).assign (← Lean.Meta.mkAppM name #[a,b,c])
   replaceMainGoal []

#print folded
#print axioms folded
#print compose
#print axioms compose
end NJE_PermutationFold
