import Lean
import NFY_Part030
import NGF_NEC_AfterstateBox

set_option autoImplicit false
namespace NGF_NED_AfterBoxComposition
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder

/-- The child execution is composed, including outer failure and divergence;
no successful child Result is an assumption. Native association remains separate. -/
theorem result (bytes : Slice U8) :
    pool_v1.pair_tree_profile.decode_pair_afterstate_boxed_v1 bytes =
      (do let reply ← NFY_NBN_AfterstateDecoderDependency.run
            (fun b => ok (NFY_NBP_DigestDecode.decoded b)) bytes
          NGF_NEC_AfterstateBox.reference reply) := by
  rw [NFY_NED_SubtreeComposition.after_decode]
  unfold pool_v1.pair_tree_profile.decode_pair_afterstate_boxed_v1
  cases h : pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1 bytes with
  | fail e => rfl
  | div => rfl
  | ok reply => cases reply <;> rfl

#print axioms result
end NGF_NED_AfterBoxComposition

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
