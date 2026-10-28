import R1Z.PV_RunJoin_SnapshotRejections29
import R1Z.PV_RunJoin_DecoderReturn29
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_DecodedDomain29
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder.pool_v1.pair_tree_profile

/-- All semantic snapshot guard facts hold on the actual decoder's return,
for arbitrary bytes. No outer compiler success or encoding premise is used. -/
theorem domain (bytes : Slice U8) (s : PoolV1PairLiveSnapshotV1)
    (h : decode_pool_v1_pair_live_snapshot_v1 bytes = ok (.Ok s)) :
    PV_RunJoin_SnapshotDomain29.Domain s :=
  (PV_RunJoin_SnapshotDomain29.success_iff s).mp (PV_RunJoin_DecoderReturn29.validated bytes s h)
#print axioms domain
end R1Z.PV_RunJoin_DecodedDomain29
