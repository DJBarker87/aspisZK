import AspisR1TerminalDecoder.Funs
set_option autoImplicit false
namespace NEC_LiveReject
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder

theorem wrong_length (bytes : Slice U8) (length : bytes.val.length≠800) :
 pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1 bytes=
 ok (.Err .WrongLength) := by
 unfold pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1
 simp only [pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES]
 have neq : Slice.len bytes≠800#usize := by
  intro equal
  have values := congrArg (fun x : Usize=>x.val) equal
  exact length values
 simp only [bne_iff_ne,neq,if_true]

#print axioms wrong_length
end NEC_LiveReject
