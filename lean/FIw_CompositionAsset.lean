import FIw_CompositionOrigins
import FIw_OpeningCanonical
import FIw_AssetSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIw_CompositionAsset
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode)
open FIw_CompositionOrigins (SemPub composition)

theorem value (pub : SemPub) (claims : Array NQ 84#usize) (point : Array NQ 10#usize)
    (lambda chi theta comp g h active : NQ) (c1 : Array NQ 16#usize) (mask : Array NQ 10#usize)
    (success : composition pub claims point lambda chi theta=ok (.Ok (comp,c1,mask,g,h,active)))
    (all : ∀ x∈claims.val,Canon x) :
    ∃ (a a1 a2 : Array NQ 16#usize)
      (selectors : pool_v1.pair_forest_copy_terminal.Selectors) (semantic : Array NQ 24#usize),
      c1=a ∧ (∀ x∈a.val,Canon x) ∧ (∀ x∈a1.val,Canon x) ∧ (∀ x∈a2.val,Canon x) ∧
      pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point=ok selectors ∧
      pool_v1.pair_forest_semantic_terminal.semantic_packed pub ⟨a,a1,a2⟩ selectors=ok semantic ∧
      ((∀ x∈selectors.high.val,Canon x) → (∀ x∈selectors.low.val,Canon x) →
        pub.asset_id.val<FIw_ScalarArithmetic.P →
        (pub.withdrawal_amount.getD 0#u32).val<FIw_ScalarArithmetic.P →
        ∃ (before : Array NQ 24#usize) (scalars : Array NQ 2#usize),
          FIw_ScalarSuffix.run pub ⟨a,a1,a2⟩ selectors before=ok semantic ∧
          pool_v1.pair_forest_semantic_terminal.add_preweighted before 92#usize scalars=ok semantic ∧
          (∀ x∈scalars.val,Canon x) ∧ scalars.val.map decode=R0P.assetFamily.residuals
            (FIw_PublicModel.ofPublic pub) (FIw_PublicModel.openings ⟨a,a1,a2⟩)
            (FIw_PublicModel.selector selectors)) := by
  obtain ⟨a,a1,a2,selectors,sops,variant,semantic,poseidon,prepared,middle,copy,iter,iter1,
    same,ga,ga1,ga2,hs,hsp,hp,hsem,hv,hcopy,hprep,hi,hi1,hmid,hfinal,hactive⟩ :=
    FIw_CompositionOrigins.reached pub claims point lambda chi theta comp g h active c1 mask success
  have ca := FIw_OpeningCanonical.z claims a all ga
  have ca1 := FIw_OpeningCanonical.succ claims a1 all ga1
  have ca2 := FIw_OpeningCanonical.xor12 claims a2 all ga2
  refine ⟨a,a1,a2,selectors,semantic,same,ca,ca1,ca2,hs,hsem,?_⟩
  intro hh hl ha hm
  exact FIw_AssetSource.value pub ⟨a,a1,a2⟩ selectors semantic ca hh hl ha hm hsem
#print axioms value
end AspisR1.FIw_CompositionAsset
end
