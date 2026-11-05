import Lean
import NGK_NFV_Envelope

set_option autoImplicit false
open Aeneas Aeneas.Std
namespace NHC_NGG_EnvelopePrefix
open NGK_NFV_Envelope
/-- Needed before runtime CPI input transport; this is a byte-value fact only. -/
theorem asq8 (profile release program : Bytes32) (kind : U8) (payment : Payment) :
    (pure profile release program kind payment).val.take 4 =
      [65#u8,83#u8,81#u8,56#u8] := by
  rw [pure_value]
  rfl
#print axioms asq8
end NHC_NGG_EnvelopePrefix

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
