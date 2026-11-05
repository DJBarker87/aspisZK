import Lean
import NHC_NGG_Ref.Funs
import NGK_NFV_RequestGuards

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NHC_NGG_Compare
abbrev Key := Array U8 32#usize
theorem ne (a b : Key) :
    core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 a b =
      ok (decide (a.val ≠ b.val)) := by
  simp only [core.array.equality.PartialEqArray.ne,NGK_NFV_RequestGuards.array,bind_tc_ok]
  by_cases h : a.val = b.val <;> simp [h]
#print axioms ne
end NHC_NGG_Compare

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
