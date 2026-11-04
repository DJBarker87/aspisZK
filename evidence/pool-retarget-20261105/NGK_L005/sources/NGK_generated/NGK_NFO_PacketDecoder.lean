import Lean
import NGK_NFO_RawDecode

set_option autoImplicit false
noncomputable section
namespace NGK_NFO_PacketDecoder
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
abbrev Output := pool_v1.pair_forest_terminal.PoolV1PairForestTerminalResultV1
abbrev Error := pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1

def run (bytes : List U8) : Result (core.result.Result Output Error) :=
  if length : bytes.length = 792 then
    NGK_NFO_RawDecode.decode (Array.to_slice (⟨bytes,length⟩ : Array U8 792#usize))
  else ok (.Err .WrongLength)

theorem on_packet (bytes : List U8) (length : bytes.length = 792) :
    run bytes = NGK_NFO_RawDecode.decode
      (Array.to_slice (⟨bytes,length⟩ : Array U8 792#usize)) := by
  simp only [run, dif_pos length]
#print axioms on_packet
end NGK_NFO_PacketDecoder

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
