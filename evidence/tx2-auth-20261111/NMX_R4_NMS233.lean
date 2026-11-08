import NMX_R4_NMSCarrier
set_option autoImplicit false
noncomputable section
namespace NMX_R4_NMS233
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets

def payload : core.result.Result Auth PE →
 core.result.Result r1_pool_adapter.AuthenticatedAsq8Accounts PE
 | .Ok a => .Ok a.erase
 | .Err e => .Err e

def typed (choices : NMX_R4_Authentication.Choices) : NMS_R2Parameterized242.Auth :=
 fun program accounts pool lane slot env observation =>
 let a := NMS_R2N_RSLPoolCarriers.args233 program accounts pool lane slot
 let c := NMX_R4_Authentication.context choices a env
 observation = NMX_R4_CallRun.map payload
  (NMX_R4_CallRun.run c
    (NMX_R4_CallRoot.auth c.owners (NMX_R4_CallContext.ops c) program accounts pool lane slot))

theorem observation (o : RSL.Obs (core.result.Result Auth PE)) :
 NMS_R2N_Interpreted.mapObs (NMS_R2N_RSLError.reply NMS_R2N_RSLPoolCarriers.authenticated)
  (NMX_R4_CallRun.map payload o) =
 NMX_R4_CallRun.map (NMX_R2_Carrier.reply NMX_R2_Carrier.auth) o := by
 cases o with
 | mk exit events =>
  cases exit with
  | abort => rfl
  | diverge => rfl
  | ret r =>
   cases r <;> simp only [NMS_R2N_Interpreted.mapObs,NMS_R2N_Interpreted.mapExit,
     NMX_R4_CallRun.map,payload,NMS_R2N_RSLError.reply,NMX_R2_Carrier.reply,
     NMX_R4_NMSCarrier.error,NMX_R4_NMSCarrier.auth]

/-- The full NMS typed233 schema, at the SAME original bounded input tuple.
All errors, four Box payloads and stopped PDA prefixes are retained. -/
theorem packet (choices : NMX_R4_Authentication.Choices) :
 NMS_R2Parameterized242.RowSpec233 LIBB_PoolLib.library LIBB_PoolLib.deployed (typed choices) := by
 intro program accounts pool lane slot env o execution
 change o = _ at execution
 subst o
 unfold NMS_R2Parameterized242.reference233
 rw [observation]
 change RSL.TX2_233.Ref LIBB_PoolLib.library LIBB_PoolLib.deployed
  (NMS_R2N_RSLPoolCarriers.args233 program accounts pool lane slot) env
  (NMX_R4_CallRun.observe
    (NMX_R4_Authentication.context choices
     (NMS_R2N_RSLPoolCarriers.args233 program accounts pool lane slot) env)
    (NMX_R4_CallRoot.auth _ _ program accounts pool lane slot))
 rw [NMX_R4_SourceFold.source,NMX_R4_NMSCarrier.args]
 exact NMX_R3_Instantiated233.native _ _ _ _ _ program accounts pool lane slot env
#print axioms observation
#print axioms packet
end NMX_R4_NMS233
end
