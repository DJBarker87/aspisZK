import FIz_SemanticAlignment
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIz_CoefficientsOnRun
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K)
open FIw_ArrayValue (canonical decoded)
open FIw_ScalarSuffix (Public Openings Selectors)
theorem on_run (p : Public) (o : Openings) (s : Selectors) (out : Array NQ 24#usize)
    (hz : canonical o.z) (hs : canonical o.succ_z) (hx : canonical o.xor12_z)
    (hh : canonical s.high) (hl : canonical s.low)
    (ha : ∀ x∈p.anchor.val,x.val<FIw_ScalarArithmetic.P)
    (hn : ∀ x∈p.nullifier.val,x.val<FIw_ScalarArithmetic.P)
    (hr : ∀ recipient,p.recipient=some recipient → ∀ x∈recipient.val,x.val<FIw_ScalarArithmetic.P)
    (hc : ∀ x∈p.change.val,x.val<FIw_ScalarArithmetic.P)
    (hf : ∀ row∈p.transition.live_snapshot.frontier.val,∀ x∈row.val,x.val<FIw_ScalarArithmetic.P)
    (hnr : ∀ x∈p.transition.candidate_afterstate.next_root.val,x.val<FIw_ScalarArithmetic.P)
    (hnf : ∀ row∈p.transition.candidate_afterstate.next_frontier.val,∀ x∈row.val,x.val<FIw_ScalarArithmetic.P)
    (hab : p.asset_id.val<FIw_ScalarArithmetic.P)
    (haw : (p.withdrawal_amount.getD 0#u32).val<FIw_ScalarArithmetic.P)
    (hm : (∑ h : Fin 64, FIv_NativeArray.value s.high h.val)=1)
    (lm : (∑ l : Fin 16, FIv_NativeArray.value s.low l.val)=1)
    (success : pool_v1.pair_forest_semantic_terminal.semantic_packed p o s=ok out) :
    canonical out ∧ decoded out=fun j=>FIx_PreweightedPack.pack
      (fun i=>R0P.SemSource.scalarLaneAt (FIw_PublicModel.ofPublic p) (FIw_PublicModel.openings o)
        (FIw_PublicModel.selector s) (4*j.val+i.val)) := by
  have native := FIy_NativeCoefficients.value p o s out hz hs hx hh hl ha hn hr hc hf hnr hnf hab haw success
  refine ⟨native.1,?_⟩
  rw [native.2,FIz_SemanticAlignment.value p o s hm lm]
#print axioms on_run
end AspisR1.FIz_CoefficientsOnRun
end
