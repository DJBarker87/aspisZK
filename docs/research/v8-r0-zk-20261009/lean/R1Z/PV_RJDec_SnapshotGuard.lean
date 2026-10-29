import R1Z.PV_RJDec_ParserR12
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_SnapshotGuard
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder PV_W_TypedEffects
variable [ProverRwFull.ExternalTypes] [ProverRwFull.ExternalFuns]
theorem wrong_length (bytes : Slice U8)
    (wrong : (Slice.len bytes != pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES) = true) :
    erase (inferInstance : ProverRwFull.ExternalFuns) (PV_RJDec_ParserR12.program bytes) =
      .ok (.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.WrongLength) := by
  simp only [PV_RJDec_ParserR12.program,wrong,Bool.true_eq,↓reduceIte,erase_pure]
#print axioms wrong_length
end R1Z.PV_RJDec_SnapshotGuard
