import R1Z.PV_RunJoin_BankMaterialized19
set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankGeometry19
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder BuilderRecordsArray
open PV_Src_Forest_BankMaterialization PV_Src_Forest_BankStep

theorem stable (pt : Parts) (cell : Nat → Nat → U32)
    (hc : ∀ lane, lane < 16 → ∀ row, row < 1024 → PV_Src_Forest_BankCells.cell pt lane row = cell lane row) :
    stableModel pt = PV_RunJoin_BankTable19.flat (PV_RunJoin_BankTable19.stableCells cell) := by
  apply BuilderRecordCanonical.array_ext
  intro k hk
  have hk' : k < 16384 := by simpa using hk
  rw [stableModel,PV_RunJoin_BankTable19.flat,tabulate_get _ _ _ hk,tabulate_get _ _ _ hk]
  have hl : LateRow k ↔ PV_RunJoin_BankTable19.late ((k%1024)/16) := by
    unfold LateRow PV_RunJoin_BankTable19.late
    omega
  unfold stableValue PV_RunJoin_BankTable19.stableCells
  rw [hc _ (by omega) _ (by omega)]
  simp only [hl]
#print axioms stable

theorem late (pt : Parts) (cell : Nat → Nat → U32)
    (hc : ∀ lane, lane < 16 → ∀ row, row < 1024 → PV_Src_Forest_BankCells.cell pt lane row = cell lane row) :
    lateModel pt = PV_RunJoin_BankTable19.flat (PV_RunJoin_BankTable19.lateCells cell) := by
  apply BuilderRecordCanonical.array_ext
  intro k hk
  have hk' : k < 16384 := by simpa using hk
  rw [lateModel,PV_RunJoin_BankTable19.flat,tabulate_get _ _ _ hk,tabulate_get _ _ _ hk]
  have hl : LateRow k ↔ PV_RunJoin_BankTable19.late ((k%1024)/16) := by
    unfold LateRow PV_RunJoin_BankTable19.late
    omega
  unfold lateValue PV_RunJoin_BankTable19.lateCells
  rw [hc _ (by omega) _ (by omega)]
  simp only [hl]
#print axioms late
end R1Z.PV_RunJoin_BankGeometry19
