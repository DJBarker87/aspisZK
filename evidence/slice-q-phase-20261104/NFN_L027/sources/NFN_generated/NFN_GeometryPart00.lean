import Lean
import NFN_PhaseTransport
import NFN_ReserveOwner
import RPz7_FIo_NativeTypes
import RPz7_FIo_NativeExternal


run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
