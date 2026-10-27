import FIw_AssetModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIw_AssetSource
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode)
open FIw_PublicModel (Public Openings Selectors)

theorem value (pub : Public) (o : Openings) (s : Selectors) (out : Array NQ 24#usize)
    (hz : ∀ x∈o.z.val,Canon x) (hh : ∀ x∈s.high.val,Canon x)
    (hl : ∀ x∈s.low.val,Canon x)
    (assetBound : pub.asset_id.val<FIw_ScalarArithmetic.P)
    (amountBound : (pub.withdrawal_amount.getD 0#u32).val<FIw_ScalarArithmetic.P)
    (success : pool_v1.pair_forest_semantic_terminal.semantic_packed pub o s=ok out) :
    ∃ (before : Array NQ 24#usize) (scalars : Array NQ 2#usize),
      FIw_ScalarSuffix.run pub o s before=ok out ∧
      pool_v1.pair_forest_semantic_terminal.add_preweighted before 92#usize scalars=ok out ∧
      (∀ x∈scalars.val,Canon x) ∧ scalars.val.map decode=R0P.assetFamily.residuals
        (FIw_PublicModel.ofPublic pub) (FIw_PublicModel.openings o) (FIw_PublicModel.selector s) := by
  obtain ⟨before,called⟩ := FIw_ScalarSuffix.reached pub o s out success
  obtain ⟨scalars,packed,canon,meaning⟩ := FIw_ScalarSuffix.value_exact pub o s before out
    hz hh hl assetBound amountBound called
  exact ⟨before,scalars,called,packed,canon,meaning.trans (FIw_AssetModel.value pub o s)⟩
#print axioms value
end AspisR1.FIw_AssetSource
end
