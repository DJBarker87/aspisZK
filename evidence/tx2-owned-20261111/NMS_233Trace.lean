import NMS_RowSpec233
set_option autoImplicit false
noncomputable section
namespace NMS_233Trace
open Aeneas Aeneas.Std AdapterRw NMS_OwnedPackets
/-- Projection is derived from the full ownership/frame/prefix law; it is not
an independent successful child or endpoint supplied to the parent. -/
theorem observation {Ambient : Type} (owners : List Nat)
 (before : NMS_RowSpec233.World Ambient)
 (source : NJU_Log.Run NMS_RowSpec233.Event
  (core.result.Result r1_pool_adapter.AuthenticatedAsq8Accounts PE))
 (outcome : NMS_RowSpec233.Outcome (NMS_RowSpec233.World Ambient))
 (law : NMS_RowSpec233.Law owners before source outcome) :
 (⟨NMS_RowSpec233.eraseValue outcome,outcome.events⟩ : NJU_Log.Run _ _) = source := by
 cases source with
 | mk result events =>
  cases outcome with
  | returned reply post trace =>
   cases reply <;> simp_all [NMS_RowSpec233.Law,NMS_RowSpec233.eraseValue,End.value,End.events]
  | stopped trace cause =>
   cases cause <;> simp_all [NMS_RowSpec233.Law,NMS_RowSpec233.eraseValue,End.value,End.events]
#print axioms observation
end NMS_233Trace
