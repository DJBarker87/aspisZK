import R1Z.PV_Src_ForestBanks

/-! Pure CopyRecords.banks totality, with successful merge guard, for all raw
records. This strengthens run_exact to the actual optional-bank wrapper. -/
set_option autoImplicit false
namespace R1Z.PV_Src_BanksTotal
open Aeneas Aeneas.Std Result
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder

theorem banks_total (r : CopyRecords) : ∃ banks, CopyRecords.banks r = ok (some banks) := by
  obtain ⟨pt,hpt⟩ := PV_Src_ForestPartsTotal.parts_total r.w r.p
  obtain ⟨merged,out,hb,hc,_,_⟩ := PV_Src_Forest_PartsComplete.banks_columns r.w r.p pt hpt
  rw [CopyRecords.banks,hb]
  simp only [bind_tc_ok,↓reduceIte]
  rw [PV_Src_Forest_Columns.columns_eq]
  simp only [bind_tc_ok]
  rw [PV_Src_Forest_Columns.columns_eq]
  simp only [bind_tc_ok]
  rw [hc]
  exact ⟨_,rfl⟩

#print axioms banks_total
end R1Z.PV_Src_BanksTotal
