import NNH_RawOptionOk
import LIBB_PoolDecoders
set_option autoImplicit false
noncomputable section
namespace NNH_RequestOk
open Aeneas Aeneas.Std AdapterRw NND_Carrier NNH_Libraries

theorem decode (b : Slice U8) (q : LIBB_PoolCarriers.Request)
 (success : L.decodeRequest (bytes b)=some q) :
 AspisR1.NFY_JHd_RequestNative.decode b=.ok (.Ok q) := by
 have mapped := LIBB_PoolDecoders.decode_root b
 change LIBB_PoolDecoders.decodeRequest (LIB_Carriers.bytes b)=some q at success
 rw [success] at mapped
 obtain ⟨a,run,same⟩ := NNH_RawOptionOk.value id _ q mapped
 cases same
 exact run

theorem nullifier (q : LIBB_PoolCarriers.Request) :
 NMS_RequestModels.nullifier q.«public»=.ok (LIBB_PoolDecoders.nullifier q) := by
 cases q.«public» <;> rfl

theorem lane (q : LIBB_PoolCarriers.Request) (out : UInt8)
 (success : L.outputLane (L.reqNullifier q)=some out) :
 ∃ native,NMS_RequestModels.outputLane (LIBB_PoolDecoders.nullifier q)=.ok (.Ok native) ∧ byte native=out := by
 have mapped := LIBB_PoolDecoders.outputLane_source (LIBB_PoolDecoders.nullifier q)
 change LIBB_PoolDecoders.outputLane (LIBB_NullifierBytes.key (LIBB_PoolDecoders.nullifier q))=some out at success
 rw [success] at mapped
 exact NNH_RawOptionOk.value byte _ out mapped
#print axioms decode
#print axioms nullifier
#print axioms lane
end NNH_RequestOk
