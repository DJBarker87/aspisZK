import NBH_FrontierTrace
import NBH_LiveValidator
set_option autoImplicit false
noncomputable section
namespace NEM_FrontierValidatorInstance
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder

theorem after_step (a : NBH_Frontier.Frontier) (i : Usize) (bound : i.val ≤ 20) :
    (do let out ← pool_v1.pair_terminal.validate_verified_afterstate_loop.body a i
        ok (NBH_NativeFrontier.observe i out)) = ok (NBH_NativeFrontier.step a i.val) :=
  NBH_NativeFrontier.source a i bound

theorem live_step (a : NBH_Frontier.Frontier) (i : Usize) (bound : i.val ≤ 20) :
    (do let out ← pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1_loop.body a i
        ok (NBH_NativeLiveFrontier.observe i out)) = ok (NBH_NativeLiveFrontier.step a i.val) :=
  NBH_NativeLiveFrontier.source a i bound

theorem live_result_and_frame {State : Type} (s : NBH_LiveValidator.Snapshot) (state : State) :
    (pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1 s,state) =
      (ok (NBH_LiveValidator.result s),state) := by
  rw [NBH_LiveValidator.source]

theorem after_result_and_frame {State : Type} (a : NBH_Validators.Afterstate) (state : State) :
    (pool_v1.pair_terminal.validate_verified_afterstate a,state) =
      (ok (NBH_Validators.afterResult a),state) := by
  rw [NBH_Validators.afterstate]

#print axioms after_step
#print axioms live_step
#print axioms live_result_and_frame
#print axioms after_result_and_frame
end NEM_FrontierValidatorInstance
