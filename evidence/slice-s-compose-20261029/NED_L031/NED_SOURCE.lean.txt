import NED_CodecComposition
import NBN_U03
import NBN_U04
import NBP_DigestDecode
set_option autoImplicit false
noncomputable section
namespace NED_SubtreeComposition
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder

theorem digest_decode : NBN_AfterDecodeTypes.NBN_Dep_DigestDecode
    (fun b => ok (NBP_DigestDecode.decoded b)) :=
  fun b => (NBP_DigestDecode.result b).symm

theorem after_encode (a : NBH_Validators.Afterstate) :
    NBN_EncoderSummary.after atomic_statement.encode_digest_canonical a =
    pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1 a :=
  NBN_EncoderSummary.after_source _ NED_CodecComposition.digest_canonical a

theorem live_encode (s : NBH_LiveValidator.Snapshot) (out : Slice U8) :
    NBN_EncoderSummary.live atomic_statement.encode_digest_canonical s out =
    pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1 s out :=
  NBN_EncoderSummary.live_source _ NED_CodecComposition.digest_canonical s out

theorem late_encode (s : NBN_LateSummary.Statement) (out : Slice U8) :
    NBN_LateSummary.run atomic_statement.encode_digest_canonical s out =
    pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1 s out :=
  NBN_LateSummary.source _ NED_CodecComposition.digest_canonical s out

theorem after_decode (bytes : Slice U8) :
    NBN_AfterstateDecoderDependency.run (fun b => ok (NBP_DigestDecode.decoded b)) bytes =
    pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1 bytes :=
  NBN_AfterstateDecoderDependency.source _ digest_decode bytes

theorem first_byte (d : Array U32 8#usize) :
    NBN_FirstByteDependency.first atomic_statement.encode_digest_canonical d =
    pool_v1.pair_forest_accounts.first_canonical_byte d :=
  NBN_FirstByteDependency.first_source _ NED_CodecComposition.digest_raw d

theorem output_lane (d : Array U32 8#usize) :
    NBN_FirstByteDependency.lane atomic_statement.encode_digest_canonical d =
    pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1 d :=
  NBN_FirstByteDependency.lane_source _ NED_CodecComposition.digest_canonical d

#print axioms digest_decode
#print axioms after_encode
#print axioms live_encode
#print axioms late_encode
#print axioms after_decode
#print axioms first_byte
#print axioms output_lane
end NED_SubtreeComposition
