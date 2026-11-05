import Lean
import NFY_Part005

set_option autoImplicit false
noncomputable section
namespace NGE_NEQ_ParserCanonical
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder

theorem some_canonical (bytes : Array U8 4#usize) (value : U32)
    (returned : aspis_core.field.M31.from_le_bytes bytes = ok (some value)) :
    value < 2147483647#u32 := by
  rw [NBG_Atomic.m31_decode] at returned
  dsimp only at returned
  by_cases invalid : core.num.U32.from_le_bytes bytes >= 2147483647#u32
  · rw [if_pos invalid] at returned
    cases returned
  · rw [if_neg invalid] at returned
    have same : core.num.U32.from_le_bytes bytes = value := Option.some.inj (Result.ok.inj returned)
    rw [← same]
    exact lt_of_not_ge invalid

#print axioms some_canonical
end NGE_NEQ_ParserCanonical

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
