import R1Z.PV_RunJoin_SourceBanks19
import R1Z.PV_RunJoin_FixtureBanks19
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BankMaterialized19
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder BuilderRecordsArray
open PV_Src_Forest_BankMaterialization

def columns (flat : Array U32 16384#usize) :=
  tabulate 16#usize (PV_Src_Forest_Columns.column flat)
def materialized (pt : Parts) (merged : Array U32 16384#usize) : CopyBanks :=
  ⟨columns (stableModel pt),columns (lateModel pt),columns merged⟩

theorem source (w : RW) (p : RP) (pt : Parts) (hp : parts w p = ok pt) :
    ∃ merged, CopyRecords.banks ⟨w,p⟩ = ok (some (materialized pt merged)) := by
  obtain ⟨merged,hm,_⟩ := banks_table w p pt hp
  refine ⟨merged,?_⟩
  rw [CopyRecords.banks,hm]
  simp only [bind_tc_ok,if_true]
  rw [PV_Src_Forest_Columns.columns_eq,PV_Src_Forest_Columns.columns_eq,PV_Src_Forest_Columns.columns_eq]
  rfl
#print axioms source

theorem selected_eq (w : RW) (p : RP) (pt : Parts) (hp : parts w p = ok pt)
    (actual : CopyBanks) (ha : CopyRecords.banks ⟨w,p⟩ = ok (some actual))
    (withdrawal : Bool) (tail : Nat → PV_Src_PortSboxStep.State)
    (hs : stableModel pt = PV_RunJoin_BankTable19.flat
      (PV_RunJoin_BankTable19.stableCells (PV_RunJoin_BankTable19.cells (PV_RunJoin_FixtureBanks19.data withdrawal tail))))
    (hl : lateModel pt = PV_RunJoin_BankTable19.flat
      (PV_RunJoin_BankTable19.lateCells (PV_RunJoin_BankTable19.cells (PV_RunJoin_FixtureBanks19.data withdrawal tail))))
    (b : Usize) :
    PV_RunJoin_BankAggregate18.columns actual b =
      PV_RunJoin_BankAggregate18.columns (PV_RunJoin_FixtureBanks19.banks withdrawal tail) b := by
  obtain ⟨merged,hm⟩ := source w p pt hp
  have he : actual = materialized pt merged := Option.some.inj (Result.ok.inj (ha.symm.trans hm))
  rw [he]
  unfold PV_RunJoin_BankAggregate18.columns materialized PV_RunJoin_FixtureBanks19.banks PV_RunJoin_BankTable19.banks
  simp only [hs,hl,columns,PV_RunJoin_BankTable19.columns]
#print axioms selected_eq
end R1Z.PV_RunJoin_BankMaterialized19
