import LIBB_AccountCarriers
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
/-- Exact deterministic graph of the CLOSED raw account model; the Box
allocation site is separate and is never used to define the decoder law. -/
theorem master_model (b : Slice U8) :
 LIBB_ResultTotal.mapOuter (asOption master) (NJQ_Canonical.master b) =
 .ok (decodeMaster (bytes b)) := by
 have h := NMX_MasterValue.source b
 change NJQ_Canonical.mapOuter NKF_BoxModel.tail (NJQ_Canonical.master b) =
   .ok (NMX_MasterValue.decoded b) at h
 cases code : NJQ_Canonical.master b with
 | fail e => rw [code] at h; cases h
 | div => rw [code] at h; cases h
 | ok r =>
   rw [code] at h
   have hr : NKF_BoxModel.tail r = NMX_MasterValue.decoded b := Result.ok.inj h
   have hs := LIBB_AccountDecoderReuse.master_same b
   rw [LIBB_AccountCarriers.bytes b] at hs
   rw [hs, ←hr]
   simp only [LIBB_AccountCarriers.master]
   cases r <;> rfl

theorem checkpoint_model (b : Slice U8) :
 LIBB_ResultTotal.mapOuter (asOption checkpoint) (NJQ_Canonical.checkpoint b) =
 .ok (decodeCheckpoint (bytes b)) := by
 have h := NMX_CheckpointValue.source b
 change NJQ_Canonical.mapOuter NKF_BoxModel.tail (NJQ_Canonical.checkpoint b) =
   .ok (NMX_CheckpointValue.decoded b) at h
 cases code : NJQ_Canonical.checkpoint b with
 | fail e => rw [code] at h; cases h
 | div => rw [code] at h; cases h
 | ok r =>
   rw [code] at h
   have hr : NKF_BoxModel.tail r = NMX_CheckpointValue.decoded b := Result.ok.inj h
   have hs := LIBB_AccountDecoderReuse.checkpoint_same b
   rw [LIBB_AccountCarriers.bytes b] at hs
   rw [hs, ←hr]
   simp only [LIBB_AccountCarriers.checkpoint]
   cases r <;> rfl

/-- Supplying root composed at the original input and full decoder Result. -/
theorem master_root (b : Slice U8)
 (out : core.result.Result NJQ_Master.M NJQ_Master.F) (cut : NJY_Master.Cut b out) :
 asOption master (NJQ_Carrier.master_result out) = decodeMaster (bytes b) := by
 have h := master_model b
 rw [←NJQ_Canonical.master_result b out cut] at h
 exact Result.ok.inj h

theorem checkpoint_root (b : Slice U8)
 (out : core.result.Result NJQ_Checkpoint.C NJQ_Checkpoint.F)
 (cut : NJY_Checkpoint.Cut b out) :
 asOption checkpoint (NJQ_Carrier.checkpoint_result out) = decodeCheckpoint (bytes b) := by
 have h := checkpoint_model b
 rw [←NJQ_Canonical.checkpoint_result b out cut] at h
 exact Result.ok.inj h

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
