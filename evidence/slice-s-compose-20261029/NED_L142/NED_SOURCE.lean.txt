import NED_SubtreeComposition
import NEC_AfterstateBox
set_option autoImplicit false
namespace NED_AfterBoxComposition
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder

/-- The child execution is composed, including outer failure and divergence;
no successful child Result is an assumption. Native association remains separate. -/
theorem result (bytes : Slice U8) :
    pool_v1.pair_tree_profile.decode_pair_afterstate_boxed_v1 bytes =
      (do let reply ← NBN_AfterstateDecoderDependency.run
            (fun b => ok (NBP_DigestDecode.decoded b)) bytes
          NEC_AfterstateBox.reference reply) := by
  rw [NED_SubtreeComposition.after_decode]
  unfold pool_v1.pair_tree_profile.decode_pair_afterstate_boxed_v1
  cases h : pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1 bytes with
  | fail e => rfl
  | div => rfl
  | ok reply => cases reply <;> rfl

#print axioms result
end NED_AfterBoxComposition
