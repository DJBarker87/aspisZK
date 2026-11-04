import Lean
import NGK_NFO_RawDecode

set_option autoImplicit false
namespace NGK_NFO_DecodeReject
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder

theorem wrong_length (bytes : Slice U8) (different : bytes.val.length ≠ 792) :
    NGK_NFO_RawDecode.decode bytes = ok (.Err pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WrongLength) := by
  have ne : Slice.len bytes ≠ 792#usize := by
    intro eq
    apply different
    exact congrArg UScalar.val eq
  have unequal : (Slice.len bytes != 792#usize) = true := by simp [ne]
  simp only [NGK_NFO_RawDecode.decode, unequal, ↓reduceIte]
#print axioms wrong_length
end NGK_NFO_DecodeReject

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
