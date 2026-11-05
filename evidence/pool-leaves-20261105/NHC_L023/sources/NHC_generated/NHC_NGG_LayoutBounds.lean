import Lean
import NHC_NGG_LayoutValue

set_option autoImplicit false
open Aeneas Aeneas.Std
namespace NHC_NGG_LayoutBounds
open NHC_NGG_LayoutValue
/-- All seven meta indices are within the exact accepted account count. -/
def metaIndices (rollover withdrawal : Bool) : List Nat :=
 let l := fields rollover withdrawal
 [l.proof_index.val,0,1,2,l.registry_start.val,l.registry_start.val+1,l.verifier_checkpoint_index.val]
theorem metas (rollover withdrawal : Bool) (i : Nat)
    (present : i ∈ metaIndices rollover withdrawal) :
    i < (expected rollover withdrawal).val := by
 cases rollover <;> cases withdrawal <;>
   simp only [metaIndices,fields,expected,List.mem_cons,List.not_mem_nil,or_false,
     Bool.false_eq_true,ite_false,ite_true] at present ⊢ <;>
   rcases present with h|h|h|h|h|h|h <;> subst i <;> decide
#print axioms metas

theorem windows (rollover withdrawal : Bool) :
 (fields rollover withdrawal).registry_start.val+2 ≤ (expected rollover withdrawal).val ∧
 (withdrawal = true → (fields rollover withdrawal).token_start.val+5 ≤ (expected rollover withdrawal).val) := by
 cases rollover <;> cases withdrawal <;> decide
#print axioms windows
end NHC_NGG_LayoutBounds

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
