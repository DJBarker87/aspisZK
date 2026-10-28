import R1Z.PV_RunJoin_BankIdentification20
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceColumns20
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults

theorem source (w : RW) (p : RP) (pt : Parts) (hp : parts w p = ok pt)
    (actual : CopyBanks) (ha : CopyRecords.banks ⟨w,p⟩ = ok (some actual)) :
    (∀ c, c < 16 → (actual.merged.val[c]!).val.length = 1024) ∧
    ∀ c r, PV_Src_Forest_Columns.read actual.merged c r = copyCellMerged (wordWitness w) (wordPublic p) c r := by
  obtain ⟨merged,out,hm,ho,hlen,hread⟩ := PV_Src_Forest_PartsComplete.banks_columns w p pt hp
  let bank : CopyBanks := ⟨PV_RunJoin_BankMaterialized19.columns (PV_Src_Forest_BankMaterialization.stableModel pt),
    PV_RunJoin_BankMaterialized19.columns (PV_Src_Forest_BankMaterialization.lateModel pt),out⟩
  have hs : CopyRecords.banks ⟨w,p⟩ = ok (some bank) := by
    rw [CopyRecords.banks,hm]
    simp only [bind_tc_ok,if_true]
    rw [PV_Src_Forest_Columns.columns_eq,PV_Src_Forest_Columns.columns_eq,ho]
    rfl
  have he : actual = bank := Option.some.inj (Result.ok.inj (ha.symm.trans hs))
  rw [he]
  exact ⟨hlen,hread⟩
#print axioms source

theorem transfer :
    (∀ c, c < 16 → (PV_RunJoin_SourceBanks19.transferBank.merged.val[c]!).val.length = 1024) ∧
    ∀ c r, PV_Src_Forest_Columns.read PV_RunJoin_SourceBanks19.transferBank.merged c r =
      copyCellMerged (wordWitness transferWitness) (wordPublic transferPublic) c r := by
  obtain ⟨pt,hp⟩ := PV_RunJoin_PartsTotal19.transfer
  exact source _ _ pt hp _ PV_RunJoin_SourceBanks19.transfer
#print axioms transfer

theorem withdrawal :
    (∀ c, c < 16 → (PV_RunJoin_SourceBanks19.withdrawalBank.merged.val[c]!).val.length = 1024) ∧
    ∀ c r, PV_Src_Forest_Columns.read PV_RunJoin_SourceBanks19.withdrawalBank.merged c r =
      copyCellMerged (wordWitness withdrawalWitness) (wordPublic withdrawalPublic) c r := by
  obtain ⟨pt,hp⟩ := PV_RunJoin_PartsTotal19.withdrawal
  exact source _ _ pt hp _ PV_RunJoin_SourceBanks19.withdrawal
#print axioms withdrawal
end R1Z.PV_RunJoin_SourceColumns20
