import Lean
import NFY_Part035

set_option autoImplicit false
namespace NGK_NFO_M31Roundtrip
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder

theorem canonical_word (x : U32) (canonical : x.val < 2147483647) :
    aspis_core.field.M31.from_le_bytes (core.num.U32.to_le_bytes x) = ok (some x) := by
  have bound : ¬ x ≥ aspis_core.field.P := by
    unfold aspis_core.field.P
    scalar_tac
  simp only [aspis_core.field.M31.from_le_bytes, AspisR1.NFY_JFt_DigestInjective.from_to,
    lift, bind_tc_ok, if_neg bound]
#print axioms canonical_word
end NGK_NFO_M31Roundtrip

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
