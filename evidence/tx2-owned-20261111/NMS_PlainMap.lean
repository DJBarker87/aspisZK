import NMS_TryFold
set_option autoImplicit false
namespace NMS_PlainMap
open Aeneas Aeneas.Std AdapterRw NMS_RowSpec242

theorem rust_identity {A : Type} : (NMS_LogMap.rust id : NMS_TryFold.R A → NMS_TryFold.R A) = id := by
 funext r
 cases r <;> rfl

theorem record {Ambient A : Type} (make : Result A → RawEvent)
 (ordinary : ∀ r, Plain (make r)) (reply : Result A) :
 NMS_LogMap.run (Event.erase (Ambient := Ambient)) id
  (NJU_Log.record (fun r => Event.plain (make r) (ordinary r)) reply) =
 NJU_Log.record make reply := by
 simp only [NMS_LogMap.run,NJU_Log.record,NMS_LogMap.result_id,
  List.map_cons,List.map_nil,Event.erase]

theorem record_rust {Ambient A : Type} (make : Result (NMS_TryFold.R A) → RawEvent)
 (ordinary : ∀ r, Plain (make r)) (reply : Result (NMS_TryFold.R A)) :
 NMS_LogMap.run (Event.erase (Ambient := Ambient)) (NMS_LogMap.rust id)
  (NJU_Log.record (fun r => Event.plain (make r) (ordinary r)) reply) =
 NJU_Log.record make reply := by
 rw [rust_identity]
 exact record make ordinary reply

theorem lift_rust {Ambient A : Type} (reply : Result (NMS_TryFold.R A)) :
 NMS_LogMap.run (Event.erase (Ambient := Ambient)) (NMS_LogMap.rust id)
  (liftM reply : NJU_Log.Run (Event Ambient) _) =
 (liftM reply : NJU_Log.Run RawEvent _) := by
 rw [rust_identity,NMS_TryFold.lifted,NMS_LogMap.result_id]
#print axioms rust_identity
#print axioms record
#print axioms record_rust
#print axioms lift_rust

theorem residual {Ambient A B : Type} (value : A → B)
 (r : core.result.Result core.convert.Infallible NMS_OwnedPackets.PE) :
 NMS_LogMap.run (Event.erase (Ambient := Ambient)) (NMS_LogMap.rust value)
  (liftM (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
   A (core.convert.FromSame NMS_OwnedPackets.PE) r)) =
 (liftM (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
   B (core.convert.FromSame NMS_OwnedPackets.PE) r) : NJU_Log.Run RawEvent _) := by
 cases r with
 | Ok never => cases never
 | Err error => rfl
#print axioms residual
end NMS_PlainMap
