import R1Z.PV_RunJoin_SourceBankValidation19
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PartsCells19
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder BuilderRecordsArray

def tail (pt : Parts) (row : Nat) : PV_Src_PortSboxStep.State :=
  tabulate 16#usize (fun lane => if row < 96 then pt.path.val[row*16+lane]!
    else pt.aux.val[(row-96)*16+lane]!)

theorem cells (pt : Parts) (withdrawal : Bool)
    (blocks : ∀ b, b < 57 → ∀ row, row < 16 → ∀ lane, lane < 16 →
      (pt.blocks.val[b]!).val[row*16+lane]! =
        ((PV_RunJoin_FixtureBanks19.certificate withdrawal b).row row).val[lane]!) :
    ∀ lane, lane < 16 → ∀ row, row < 1024 →
      PV_Src_Forest_BankCells.cell pt lane row =
        PV_RunJoin_BankTable19.cells (PV_RunJoin_FixtureBanks19.data withdrawal (tail pt)) lane row := by
  intro lane hl row hr
  unfold PV_Src_Forest_BankCells.cell PV_RunJoin_BankTable19.cells
  rw [if_pos hl]
  unfold PV_RunJoin_FixtureBanks19.data
  by_cases hb : row < 912
  · rw [if_pos hb,if_pos (by omega)]
    exact blocks (row/16) (by omega) (row%16) (by omega) lane hl
  · rw [if_neg hb]
    rw [if_neg (show ¬ row/16 < 57 by omega)]
    have hi : (row/16-57)*16+row%16 = row-912 := by omega
    rw [hi,tail,tabulate_get _ _ lane (by simpa using hl)]
    by_cases hp : row < 1008
    · rw [if_pos hp,if_pos (by omega)]
    · rw [if_neg hp,if_neg (by omega)]
      have ha : row-912-96 = row-1008 := by omega
      rw [ha]
#print axioms cells
end R1Z.PV_RunJoin_PartsCells19
