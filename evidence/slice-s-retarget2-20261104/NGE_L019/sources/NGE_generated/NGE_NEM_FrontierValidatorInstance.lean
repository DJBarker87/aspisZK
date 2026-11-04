import Lean
import NFY_Part006
import NFY_Part005

set_option autoImplicit false
noncomputable section
namespace NGE_NEM_FrontierValidatorInstance
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder

theorem after_step (a : NBH_Frontier.Frontier) (i : Usize) (bound : i.val ≤ 20) :
    (do let out ← pool_v1.pair_terminal.validate_verified_afterstate_loop.body a i
        ok (NFY_NBH_NativeFrontier.observe i out)) = ok (NFY_NBH_NativeFrontier.step a i.val) :=
  NFY_NBH_NativeFrontier.source a i bound

theorem live_step (a : NBH_Frontier.Frontier) (i : Usize) (bound : i.val ≤ 20) :
    (do let out ← pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1_loop.body a i
        ok (NFY_NBH_NativeLiveFrontier.observe i out)) = ok (NFY_NBH_NativeLiveFrontier.step a i.val) :=
  NFY_NBH_NativeLiveFrontier.source a i bound

theorem live_result_and_frame {State : Type} (s : NFY_NBH_LiveValidator.Snapshot) (state : State) :
    (pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1 s,state) =
      (ok (NFY_NBH_LiveValidator.result s),state) := by
  rw [NFY_NBH_LiveValidator.source]

theorem after_result_and_frame {State : Type} (a : NFY_NBH_Validators.Afterstate) (state : State) :
    (pool_v1.pair_terminal.validate_verified_afterstate a,state) =
      (ok (NFY_NBH_Validators.afterResult a),state) := by
  rw [NFY_NBH_Validators.afterstate]

#print axioms after_step
#print axioms live_step
#print axioms live_result_and_frame
#print axioms after_result_and_frame
end NGE_NEM_FrontierValidatorInstance

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
