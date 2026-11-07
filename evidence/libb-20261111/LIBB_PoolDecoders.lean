import LIBB_NullifierBytes
import LIBB_V1DecoderValues
import NMS_R2DecoderImage
import NMS_R2LaneModel
import NMS_R2NullifierCarrier
set_option autoImplicit false
noncomputable section
namespace LIBB_PoolDecoders
open Aeneas Aeneas.Std
open LIBB_V1DecoderValues (asOption)
open LIBB_PoolCarriers
abbrev decodeRequest := NMS_R2DecoderImage.decode
def reqProfile (q : Request) : RSL.B32 := LIB_Carriers.b32 q.verifier_profile
def reqRelease (q : Request) : RSL.B32 := LIB_Carriers.b32 q.verifier_release
def reqPoolProgram (q : Request) : RSL.B32 := LIB_Carriers.b32 q.pool_program
/-- The full eight-word nullifier, on the SAME adopted request carrier. -/
def nullifier (q : Request) : LIBB_NullifierBytes.Digest :=
 match q.«public» with | .PrivateTransfer p => p.nullifier | .Withdrawal p => p.nullifier
def reqNullifier (q : Request) : RSL.B32 := LIBB_NullifierBytes.key (nullifier q)
/-- The inverse is a representation conversion; the value is the CLOSED156
model. It is never the image of a native Cut or Windows relation. -/
def outputLane (b : RSL.B32) : Option UInt8 :=
 match LIBB_NullifierBytes.digest b with
 | none => none
 | some d => asOption NND_Carrier.byte (NFY_NBN_OutputLane.result d)

theorem decode_root (b : Slice U8) :
 LIBB_ResultTotal.mapOuter (asOption id) (AspisR1.NFY_JHd_RequestNative.decode b) =
 .ok (decodeRequest (LIB_Carriers.bytes b)) := by
 obtain ⟨decoded, run⟩ := NMS_R2RequestTotal.total b
 have same := NMS_R2DecoderImage.same_input b
 unfold NMS_R2DecoderImage.option at same
 rw [run] at same
 apply Eq.trans _ (congrArg Result.ok same.symm)
 have h := congrArg (LIBB_ResultTotal.mapOuter (asOption (id : Request → Request))) run
 exact h.trans (by cases decoded <;> rfl)

theorem nullifier_source (q : Request) :
 LIBB_ResultTotal.mapOuter LIBB_NullifierBytes.key (NMS_RequestModels.nullifier q.«public») =
 .ok (reqNullifier q) := by
 unfold reqNullifier nullifier NMS_RequestModels.nullifier
 cases q.«public» <;> rfl

theorem outputLane_source (d : LIBB_NullifierBytes.Digest) :
 LIBB_ResultTotal.mapOuter (asOption NND_Carrier.byte) (NMS_RequestModels.outputLane d) =
 .ok (outputLane (LIBB_NullifierBytes.key d)) := by
 rw [NMS_R2LaneModel.source]
 simp only [outputLane,LIBB_NullifierBytes.roundtrip]
 unfold NMS_R2LaneModel.result
 cases NFY_NBN_OutputLane.result d <;> rfl

theorem profile_exact (q : Request) : reqProfile q = LIB_Carriers.b32 q.verifier_profile := rfl
theorem release_exact (q : Request) : reqRelease q = LIB_Carriers.b32 q.verifier_release := rfl
theorem program_exact (q : Request) : reqPoolProgram q = LIB_Carriers.b32 q.pool_program := rfl

theorem decode_returns (b : RSL.Bytes) (env : RSL.Env) :
 NND_Returned.Returns (RSL.Spec.pure (decodeRequest b)) env (decodeRequest b) := NND_Returned.pure env _
theorem lane_returns (b : RSL.B32) (env : RSL.Env) :
 NND_Returned.Returns (RSL.Spec.pure (outputLane b)) env (outputLane b) := NND_Returned.pure env _
#print axioms decode_root
#print axioms nullifier_source
#print axioms outputLane_source
#print axioms profile_exact
#print axioms release_exact
#print axioms program_exact
#print axioms decode_returns
#print axioms lane_returns
end LIBB_PoolDecoders
end
