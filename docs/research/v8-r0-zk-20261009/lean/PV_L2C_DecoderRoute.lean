import PV_L2C_CanonicalCaller
import PV_L2C_RecordRange
import PV_L2C_AdmissionPairRange
set_option autoImplicit false
noncomputable section
namespace PV_L2C_DecoderRoute
open Aeneas Aeneas.Std Result R1Z PV_RunJoin_Outer30
local instance : BuilderForestAdmissionPort.ExternalLinear := PV_RunJoin_ShippedExternal.E_shipped
local instance : BuilderForestAdmissionPort.Records := PV_RunJoin_UniversalRecords22.shipped
local instance : LaneRoot := PV_RunJoin_LaneABI31.native

/-- Explicit decoder/generator route restriction, additional to the broader
D370 success domain. The original HonestInput carrier is unchanged. Origin
stores successful source calls and never assumes N3 or trace range. -/
structure Transfer extends PV_L2C_CanonicalCaller.Transfer where
  recipientOwner : PV_L2C_DigestOrigin.Origin witness.recipient.owner_key
  recipientSalt : PV_L2C_DigestOrigin.Origin witness.recipient.salt
  changeOwner : PV_L2C_DigestOrigin.Origin witness.change.owner_key
  changeSalt : PV_L2C_DigestOrigin.Origin witness.change.salt

structure Withdrawal extends PV_L2C_CanonicalCaller.Withdrawal where
  changeOwner : PV_L2C_DigestOrigin.Origin witness.change.owner_key
  changeSalt : PV_L2C_DigestOrigin.Origin witness.change.salt

theorem transfer_fields (t : Transfer) (root : Array U32 8#usize) :
    PV_L2C_RecordRange.Fields (PV_RunJoin_OuterChecked30.transferInput t.pubInput t.witness root
      (PV_RunJoin_CodecOuter30.snapshot t.snapshot) t.compiled) := by
  have hc := (PV_RunJoin_CodecOuter30.returned _ _ _ _ t.success).2
  have facts := PV_RunJoin_OuterCommonFacts30.transfer _ _ _ _ _ hc
  have coords := PV_L2C_AdmissionPairRange.coordinates _ facts.pair_validation
  refine ⟨facts.key,facts.salt,coords.1,coords.2,?_,t.changeOwner,t.changeSalt⟩
  intro note he
  change some (PV_RunJoin_OuterABI30.noteToForest t.witness.recipient) = some note at he
  cases Option.some.inj he
  exact ⟨t.recipientOwner,t.recipientSalt⟩
#print axioms transfer_fields

theorem withdrawal_fields (t : Withdrawal) (root : Array U32 8#usize) :
    PV_L2C_RecordRange.Fields (PV_RunJoin_OuterChecked30.withdrawalInput t.pubInput t.witness root
      (PV_RunJoin_CodecOuter30.snapshot t.snapshot) t.compiled) := by
  have hc := (PV_RunJoin_CodecOuter30.returned _ _ _ _ t.success).2
  have facts := PV_RunJoin_OuterCommonFacts30.withdrawal _ _ _ _ _ hc
  have coords := PV_L2C_AdmissionPairRange.coordinates _ facts.pair_validation
  refine ⟨facts.key,facts.salt,coords.1,coords.2,?_,t.changeOwner,t.changeSalt⟩
  intro note he
  change none = some note at he
  cases he
#print axioms withdrawal_fields
end PV_L2C_DecoderRoute
