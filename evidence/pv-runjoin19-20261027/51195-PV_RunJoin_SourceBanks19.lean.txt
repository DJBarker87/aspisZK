import R1Z.PV_RunJoin_PartsTotal19
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceBanks19
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults

theorem source (w : RW) (p : RP) (hw : WitnessOk (wordWitness w)) :
    ∃ banks, CopyRecords.banks ⟨w,p⟩ = ok (some banks) := by
  obtain ⟨pt,hp⟩ := PV_RunJoin_PartsTotal19.source w p hw
  obtain ⟨merged,hm,_⟩ := PV_Src_Forest_BankMaterialization.banks_table w p pt hp
  rw [CopyRecords.banks,hm]
  simp only [bind_tc_ok,if_true]
  rw [PV_Src_Forest_Columns.columns_eq,PV_Src_Forest_Columns.columns_eq,PV_Src_Forest_Columns.columns_eq]
  exact ⟨_,rfl⟩
#print axioms source

def transferBank : CopyBanks := Classical.choose (source transferWitness transferPublic transfer_checked)
def withdrawalBank : CopyBanks := Classical.choose (source withdrawalWitness withdrawalPublic withdrawal_checked)

theorem transfer : CopyRecords.banks ⟨transferWitness,transferPublic⟩ = ok (some transferBank) :=
  Classical.choose_spec (source transferWitness transferPublic transfer_checked)
#print axioms transfer

theorem withdrawal : CopyRecords.banks ⟨withdrawalWitness,withdrawalPublic⟩ = ok (some withdrawalBank) :=
  Classical.choose_spec (source withdrawalWitness withdrawalPublic withdrawal_checked)
#print axioms withdrawal
end R1Z.PV_RunJoin_SourceBanks19
