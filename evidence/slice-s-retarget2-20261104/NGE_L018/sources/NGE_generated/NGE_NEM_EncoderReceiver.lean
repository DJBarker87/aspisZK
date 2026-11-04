import Lean
import NGE_NEM_KindInstance

set_option autoImplicit false
noncomputable section
namespace NGE_NEM_EncoderReceiver
open Aeneas Aeneas.Std
/-- The terminal encoder's sequence carrier has exactly the primitive U64 width. -/
theorem sequence_width (c : NBD_TerminalProjection.Common) :
    (core.num.U64.to_le_bytes c.checkpoint_sequence).val.length=8 :=
  (core.num.U64.to_le_bytes c.checkpoint_sequence).property
#print axioms sequence_width
end NGE_NEM_EncoderReceiver

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
