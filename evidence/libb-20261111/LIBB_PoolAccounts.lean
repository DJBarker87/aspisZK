import LIBB_AccountGraph
import LIBB_ResultTotal
import LIBB_V1DecoderValues
import NJY_Roots
import NND_MasterCarrier
import NND_CheckpointCarrier
set_option autoImplicit false
noncomputable section
namespace LIBB_PoolAccounts
open Aeneas Aeneas.Std NND_Carrier
open LIBB_V1DecoderValues (asOption)
abbrev decodeMaster := LIBB_AccountDecoderReuse.master
abbrev decodeCheckpoint := LIBB_AccountDecoderReuse.checkpoint
abbrev master_model := LIBB_AccountGraph.master_model
abbrev checkpoint_model := LIBB_AccountGraph.checkpoint_model

/-- Supplying root composed at the original input and full decoder Result. -/
theorem master_root (b : Slice U8)
 (out : core.result.Result NJQ_Master.M NJQ_Master.F) (cut : NJY_Master.Cut b out) :
 asOption master (NJQ_Carrier.master_result out) = decodeMaster (bytes b) := by
 exact Result.ok.inj ((congrArg (LIBB_ResultTotal.mapOuter (asOption master))
  (NJQ_Canonical.master_result b out cut)).trans (master_model b))

theorem checkpoint_root (b : Slice U8)
 (out : core.result.Result NJQ_Checkpoint.C NJQ_Checkpoint.F)
 (cut : NJY_Checkpoint.Cut b out) :
 asOption checkpoint (NJQ_Carrier.checkpoint_result out) = decodeCheckpoint (bytes b) := by
 exact Result.ok.inj ((congrArg (LIBB_ResultTotal.mapOuter (asOption checkpoint))
  (NJQ_Canonical.checkpoint_result b out cut)).trans (checkpoint_model b))

theorem master_returns (b : RSL.Bytes) (env : RSL.Env) :
 NND_Returned.Returns (RSL.Spec.pure (decodeMaster b)) env (decodeMaster b) :=
 NND_Returned.pure env _
theorem checkpoint_returns (b : RSL.Bytes) (env : RSL.Env) :
 NND_Returned.Returns (RSL.Spec.pure (decodeCheckpoint b)) env (decodeCheckpoint b) :=
 NND_Returned.pure env _
#print axioms master_model
#print axioms checkpoint_model
#print axioms master_root
#print axioms checkpoint_root
#print axioms master_returns
#print axioms checkpoint_returns
end LIBB_PoolAccounts
end
