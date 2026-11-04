import Lean
import NGK_NFO_PacketDecoder

set_option autoImplicit false
namespace NGK_NFO_PacketAccepted
open Aeneas Aeneas.Std Result

theorem accepted (bytes : List U8) (value : NGK_NFO_PacketDecoder.Output)
    (success : NGK_NFO_PacketDecoder.run bytes = ok (.Ok value)) :
    ∃ width : bytes.length = 792,
      NGK_NFO_RawDecode.decode (Array.to_slice (⟨bytes,width⟩ : Array U8 792#usize)) = ok (.Ok value) := by
  by_cases width : bytes.length = 792
  · exact ⟨width,(NGK_NFO_PacketDecoder.on_packet bytes width).symm.trans success⟩
  · simp only [NGK_NFO_PacketDecoder.run, dif_neg width] at success
    cases success
#print axioms accepted
end NGK_NFO_PacketAccepted

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
