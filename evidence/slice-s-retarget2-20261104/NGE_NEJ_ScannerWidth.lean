import Lean
import NGE_NEJ_ScannerFramed

set_option autoImplicit false
namespace NGE_NEJ_ScannerWidth
open Aeneas Aeneas.Std

/-- Digest::len is the length of a fixed eight-word carrier, not a callback.
The native step executes the actual len operation without stubbing it. -/
theorem width (digest : Array U32 8#usize) : digest.val.length = 8 := by
  exact digest.property

#print axioms width
end NGE_NEJ_ScannerWidth

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
