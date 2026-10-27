import RPv_FIy_PublicDigestSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIy_PublicDigest
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K)
open FIw_ArrayValue (canonical decoded)
open FIy_PublicDigestPrefix (Public Openings)
open FIy_FrontierStep (Selectors)

def model (p : Public) (o : Openings) (s : Selectors) : Fin (8#usize).val → K :=
  FIy_PublicDigestSuffix.model p o s p.transition.live_snapshot
    (FIy_FrontierLoop.model p.transition.live_snapshot s o.z 20 0 (FIy_PublicDigestPrefix.model p o s))

theorem value (p : Public) (o : Openings) (s : Selectors) (out : Array NQ 8#usize)
    (hz : canonical o.z) (hh : canonical s.high) (hl : canonical s.low)
    (ha : ∀ x∈p.anchor.val,x.val<FIw_ScalarArithmetic.P)
    (hn : ∀ x∈p.nullifier.val,x.val<FIw_ScalarArithmetic.P)
    (hr : ∀ recipient,p.recipient=some recipient → ∀ x∈recipient.val,x.val<FIw_ScalarArithmetic.P)
    (hc : ∀ x∈p.change.val,x.val<FIw_ScalarArithmetic.P)
    (hf : ∀ row∈p.transition.live_snapshot.frontier.val,∀ x∈row.val,x.val<FIw_ScalarArithmetic.P)
    (hnr : ∀ x∈p.transition.candidate_afterstate.next_root.val,x.val<FIw_ScalarArithmetic.P)
    (hnf : ∀ row∈p.transition.candidate_afterstate.next_frontier.val,∀ x∈row.val,x.val<FIw_ScalarArithmetic.P)
    (success : pool_v1.pair_forest_semantic_terminal.public_digest_lanes p o s=ok out) :
    canonical out ∧ decoded out=model p o s := by
  rw [FIy_PublicDigestSource.factor] at success
  obtain ⟨initial,hinitial,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨⟨middle,src⟩,hmiddle,tail⟩ := FIv_Map.bind_success _ _ _ success
  have first := FIy_PublicDigestPrefix.value p o s initial hz hh hl ha hn hr hc hinitial
  have middleValue := FIy_Frontier20.value o.z s initial middle p.transition.live_snapshot src hz hh hl first.1 hf hmiddle
  have same := middleValue.1
  subst src
  have ending := FIy_PublicDigestSuffix.value p o s middle out p.transition.live_snapshot hz hh hl middleValue.2.1 hnr hnf tail
  refine ⟨ending.1,?_⟩
  rw [ending.2,middleValue.2.2,first.2]
  rfl
#print axioms value
end AspisR1.FIy_PublicDigest
end
