import R1Z.PV_RunJoin_BankGeometry19
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceBankValidation19
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open pair_forest_copy_builder PV_RunJoin_ReferenceFixtureResults
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary

theorem source (w : RW) (p : RP) (pt : Parts) (hp : parts w p = ok pt)
    (actual : CopyBanks) (ha : CopyRecords.banks ⟨w,p⟩ = ok (some actual))
    (withdrawal : Bool) (tail : Nat → PV_Src_PortSboxStep.State)
    (cells : ∀ lane, lane < 16 → ∀ row, row < 1024 →
      PV_Src_Forest_BankCells.cell pt lane row =
        PV_RunJoin_BankTable19.cells (PV_RunJoin_FixtureBanks19.data withdrawal tail) lane row) :
    pair_forest_trace.validate_forest_poseidon_rows actual = ok (.Ok ()) := by
  apply PV_RunJoin_BankAggregate18.rows actual
  intro b hb
  rw [PV_RunJoin_BankMaterialized19.selected_eq w p pt hp actual ha withdrawal tail
    (PV_RunJoin_BankGeometry19.stable pt _ cells) (PV_RunJoin_BankGeometry19.late pt _ cells) b]
  cases withdrawal
  · exact PV_RunJoin_FixtureBanks19.transfer_blocks tail b hb
  · exact PV_RunJoin_FixtureBanks19.withdrawal_blocks tail b hb
#print axioms source

theorem transfer (pt : Parts) (hp : parts transferWitness transferPublic = ok pt)
    (tail : Nat → PV_Src_PortSboxStep.State)
    (cells : ∀ lane, lane < 16 → ∀ row, row < 1024 →
      PV_Src_Forest_BankCells.cell pt lane row =
        PV_RunJoin_BankTable19.cells (PV_RunJoin_FixtureBanks19.data false tail) lane row) :
    pair_forest_trace.validate_forest_poseidon_rows PV_RunJoin_SourceBanks19.transferBank = ok (.Ok ()) :=
  source _ _ pt hp _ PV_RunJoin_SourceBanks19.transfer false tail cells
#print axioms transfer

theorem withdrawal (pt : Parts) (hp : parts withdrawalWitness withdrawalPublic = ok pt)
    (tail : Nat → PV_Src_PortSboxStep.State)
    (cells : ∀ lane, lane < 16 → ∀ row, row < 1024 →
      PV_Src_Forest_BankCells.cell pt lane row =
        PV_RunJoin_BankTable19.cells (PV_RunJoin_FixtureBanks19.data true tail) lane row) :
    pair_forest_trace.validate_forest_poseidon_rows PV_RunJoin_SourceBanks19.withdrawalBank = ok (.Ok ()) :=
  source _ _ pt hp _ PV_RunJoin_SourceBanks19.withdrawal true tail cells
#print axioms withdrawal
end R1Z.PV_RunJoin_SourceBankValidation19
