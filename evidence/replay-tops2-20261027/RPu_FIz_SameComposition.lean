import RPu_FIy_PartialRoot
import RPu_FIz_SemanticAlignment
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIz_SameComposition
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon)
open FIw_ArrayValue (canonical decoded)
open FIw_ScalarSuffix (Public Openings Selectors)
theorem on_run (p : Public) (claims : Array NQ 84#usize) (point : Array NQ 10#usize)
    (lambda chi theta comp g h active : NQ) (c1 : Array NQ 16#usize) (mask : Array NQ 10#usize)
    (hclaims : canonical claims)
    (ha : ∀ x∈p.anchor.val,x.val<FIw_ScalarArithmetic.P)
    (hn : ∀ x∈p.nullifier.val,x.val<FIw_ScalarArithmetic.P)
    (hr : ∀ recipient,p.recipient=some recipient → ∀ x∈recipient.val,x.val<FIw_ScalarArithmetic.P)
    (hc : ∀ x∈p.change.val,x.val<FIw_ScalarArithmetic.P)
    (hf : ∀ row∈p.transition.live_snapshot.frontier.val,∀ x∈row.val,x.val<FIw_ScalarArithmetic.P)
    (hnr : ∀ x∈p.transition.candidate_afterstate.next_root.val,x.val<FIw_ScalarArithmetic.P)
    (hnf : ∀ row∈p.transition.candidate_afterstate.next_frontier.val,∀ x∈row.val,x.val<FIw_ScalarArithmetic.P)
    (hab : p.asset_id.val<FIw_ScalarArithmetic.P)
    (haw : (p.withdrawal_amount.getD 0#u32).val<FIw_ScalarArithmetic.P)
    (success : pool_v1.pair_forest_semantic_terminal.composition_parts p claims point lambda chi theta=
      ok (.Ok (comp,c1,mask,g,h,active))) :
    ∃ (a a1 a2 : Array NQ 16#usize) (s : Selectors) (semantic : Array NQ 24#usize),
      c1=a ∧ canonical a ∧ canonical a1 ∧ canonical a2 ∧
      pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point=ok s ∧
      pool_v1.pair_forest_semantic_terminal.semantic_packed p ⟨a,a1,a2⟩ s=ok semantic ∧
      (canonical s.high → canonical s.low →
        (∑ h : Fin 64, FIv_NativeArray.value s.high h.val)=1 →
        (∑ l : Fin 16, FIv_NativeArray.value s.low l.val)=1 →
        canonical semantic ∧ decoded semantic=fun j=>FIx_PreweightedPack.pack
          (fun i=>R0P.SemSource.scalarLaneAt (FIw_PublicModel.ofPublic p)
            (FIw_PublicModel.openings ⟨a,a1,a2⟩) (FIw_PublicModel.selector s) (4*j.val+i.val))) := by
  obtain ⟨a,a1,a2,s,semantic,same,ca,ca1,ca2,hs,hsem,value⟩ :=
    FIy_PartialRoot.on_run p claims point lambda chi theta comp g h active c1 mask
      hclaims ha hn hr hc hf hnr hnf hab haw success
  refine ⟨a,a1,a2,s,semantic,same,ca,ca1,ca2,hs,hsem,?_⟩
  intro hh hl hm lm
  have v := value hh hl
  exact ⟨v.1,v.2.trans (FIz_SemanticAlignment.value p ⟨a,a1,a2⟩ s hm lm)⟩
#print axioms on_run
end AspisR1.FIz_SameComposition
end
