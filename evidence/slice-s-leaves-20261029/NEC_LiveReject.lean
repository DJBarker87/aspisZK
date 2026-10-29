import NEC_LiveConstants
set_option autoImplicit false
namespace NEC_LiveReject
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder

theorem wrong_length (bytes : Slice U8) (length : bytes.val.length≠800) :
 pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1 bytes=
 ok (.Err .WrongLength) := by
 have neq : Slice.len bytes≠pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES := by
  intro equal
  rw [NEC_LiveConstants.live_width] at equal
  have values := congrArg (fun x : Usize=>x.val) equal
  exact length values
 have guard : (Slice.len bytes != pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES)=true :=
  bne_iff_ne.mpr neq
 unfold pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1
 exact if_pos guard

#print axioms wrong_length
end NEC_LiveReject
