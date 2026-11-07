import NMS_Owned242
import NMS_LogMap
import NMS_233Trace
set_option autoImplicit false
noncomputable section
namespace NMS_Owned242Cuts
open Aeneas Aeneas.Std AdapterRw NMS_OwnedPackets NMS_RowSpec242

theorem auth_value {Ambient : Type} (e : NMS_RowSpec233.Outcome (World Ambient)) :
 NMS_LogMap.result (NMS_LogMap.rust Auth.erase) e.value = NMS_RowSpec233.eraseValue e := by
 cases e with
 | returned r _ _ => cases r <;> rfl
 | stopped _ reason => cases reason <;> rfl

theorem auth_reply {Ambient : Type} (e : NMS_RowSpec233.Outcome (World Ambient)) :
 mapReply Auth.erase e.value = NMS_RowSpec233.eraseValue e := by
 rw [←NMS_LogMap.reply]
 exact auth_value e

/-- Full233 trace and Result are composed at the five original arguments.
The actual Box owners remain in the richer Event; this theorem erases them
only for the canonical source-observation projection. -/
theorem authenticate {Ambient CoreError : Type}
 (missing : AspisR1.IDa_Deployed.Uninstalled CoreError) (indexError : CoreError)
 (reservation : AspisR1.NP6_StdModel.Reservation)
 (owners : NMS_RowSpec233.Args → List Nat) (native : NMS_RowSpec233.Native Ambient)
 (packet : NMS_RowSpec233.RowSpec_233 missing indexError reservation owners native)
 (before : World Ambient) (program : solana_pubkey.Pubkey)
 (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey)
 (lane : U8) (slot : U64) :
 NMS_LogMap.run Event.erase (NMS_LogMap.rust Auth.erase)
  (NMS_Owned242.authenticate native before program accounts pool lane slot) =
 NLM_Validate242.authenticate (NLM_DeployedOps.ops missing indexError reservation)
  program accounts pool lane slot := by
 let a : NMS_RowSpec233.Args := ⟨program,accounts,pool,lane,slot⟩
 have observation := NMS_233Trace.observation (owners a) before _ (native a before)
  (packet a before).1
 simp only [NMS_LogMap.run,NMS_Owned242.authenticate,NLM_Validate242.authenticate,
  List.map_cons,List.map_nil,Event.erase,auth_value,auth_reply]
 change NJU_Log.Run.mk (NMS_RowSpec233.eraseValue (native a before))
  [NLM_Validate242.Event.authenticate program accounts pool lane slot
   ⟨NMS_RowSpec233.eraseValue (native a before),(native a before).events⟩] = _
 rw [←observation]

theorem scan {Ambient : Type} (ops : Ops) (inputs : List Nat) (auth : Auth) (bytes : Slice U8) :
 NMS_LogMap.run (Event.erase (Ambient := Ambient)) (NMS_LogMap.rust Scanned.erase)
  (NMS_Owned242.scan ops inputs auth bytes) =
 NJU_Log.record (NLM_Validate242.Event.scan bytes) (ops.op51 bytes) := by
 cases h : ops.op51 bytes with
 | ok r => cases r <;> simp only [NMS_Owned242.scan,h,mapReply,NJU_Log.record,
    NMS_LogMap.run,NMS_LogMap.result,NMS_LogMap.rust,List.map_cons,List.map_nil,Event.erase,Scanned.erase]
 | fail _ => simp only [NMS_Owned242.scan,h,mapReply,NJU_Log.record,
    NMS_LogMap.run,NMS_LogMap.result,NMS_LogMap.rust,List.map_cons,List.map_nil,Event.erase,Scanned.erase]
 | div => simp only [NMS_Owned242.scan,h,mapReply,NJU_Log.record,
    NMS_LogMap.run,NMS_LogMap.result,NMS_LogMap.rust,List.map_cons,List.map_nil,Event.erase,Scanned.erase]

theorem reconstruct {Ambient : Type} (ops : Ops) (inputs : List Nat)
 (request : Request) (auth : Auth) (candidate : Box Candidate) :
 NMS_LogMap.run (Event.erase (Ambient := Ambient)) (NMS_LogMap.rust Box.payload)
  (NMS_Owned242.reconstruct ops inputs request auth candidate) =
 NJU_Log.record (NLM_Validate242.Event.reconstruct request auth.erase candidate.payload)
  (ops.op52 request auth.erase candidate.payload) := by
 cases h : ops.op52 request auth.erase candidate.payload with
 | ok r => cases r <;> simp only [NMS_Owned242.reconstruct,h,mapReply,NJU_Log.record,
    NMS_LogMap.run,NMS_LogMap.result,NMS_LogMap.rust,List.map_cons,List.map_nil,Event.erase]
 | fail _ => simp only [NMS_Owned242.reconstruct,h,mapReply,NJU_Log.record,
    NMS_LogMap.run,NMS_LogMap.result,NMS_LogMap.rust,List.map_cons,List.map_nil,Event.erase]
 | div => simp only [NMS_Owned242.reconstruct,h,mapReply,NJU_Log.record,
    NMS_LogMap.run,NMS_LogMap.result,NMS_LogMap.rust,List.map_cons,List.map_nil,Event.erase]
#print axioms auth_value
#print axioms auth_reply
#print axioms authenticate
#print axioms scan
#print axioms reconstruct
end NMS_Owned242Cuts
