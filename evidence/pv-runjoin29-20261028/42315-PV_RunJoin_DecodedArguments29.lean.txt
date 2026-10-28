import R1Z.PV_RunJoin_DecodedFrontier29
import R1Z.PV_RunJoin_DomainSupport28
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_DecodedArguments29
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_NativeInput PV_RunJoin_PreparedPayload28

/-- Field-preserving nominal ABI adapter from the actual snapshot decoder
cohort to the forest compiler cohort. No validation or field normalization. -/
def snapshot (s : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) :
    BuilderForestAdmissionPort.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 :=
  ⟨s.pool,s.deployment_domain,s.sequence,s.next_pair_index,s.current_root,s.frontier⟩

def arguments (a : Arguments)
    (s : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : Arguments :=
  { a with snapshot := snapshot s }

/-- Actual successful decoding supplies canonical frontier words at the
compiler argument, universally over all other argument fields. -/
theorem frontier (bytes : Slice U8)
    (s : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (decoded : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1
      bytes = ok (.Ok s)) (a : Arguments)
    (c : BuilderForestAdmissionPort.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (l : Fin 20) : Canon8 (install (arguments a s) c).snapshot.frontier.val[l.val]! :=
  PV_RunJoin_DecodedFrontier29.decoded_frontier bytes s decoded l
#print axioms frontier

/-- The earlier raw-wrapper probe cannot be returned by the canonical route's
snapshot decoder, regardless of any proposed root or compilation payload. -/
theorem probe_excluded (bytes : Slice U8)
    (s : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (decoded : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1
      bytes = ok (.Ok s)) :
    s.frontier ≠ PV_RunJoin_FrontierHonesty28.frontier := by
  intro he
  have hc := PV_RunJoin_DecodedFrontier29.decoded_frontier bytes s decoded
    (⟨0,by decide⟩ : Fin 20) 0 (by decide)
  rw [he] at hc
  change PV_RunJoin_FrontierHonesty28.frontier.val[0]!.val[0]!.val < 2147483647 at hc
  rw [PV_RunJoin_FrontierHonesty28.raw_word] at hc
  omega
#print axioms probe_excluded
end R1Z.PV_RunJoin_DecodedArguments29
