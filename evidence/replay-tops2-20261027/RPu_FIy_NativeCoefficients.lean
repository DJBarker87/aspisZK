import RPu_FIy_CoefficientSource
import RPu_FIy_ScalarPacked
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIy_NativeCoefficients
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K)
open FIw_ArrayValue (canonical decoded)
open FIw_ScalarSuffix (Public Openings Selectors)
open FIx_SelectedMeaning (contribution)

def model (p : Public) (o : Openings) (s : Selectors) (j : Fin (24#usize).val) : K :=
  contribution (FIx_ScheduleModel.initial p.variant s o) 0 j.val+
  contribution (FIx_ScheduleModel.absorption p.variant s o) 16 j.val+
  contribution (FIx_PathMeaning.coefficients (FIx_PathPacked.selector s) (FIv_NativeArray.value o.z 0)
    (FIv_NativeArray.value o.z) (FIv_NativeArray.value o.succ_z)) 32 j.val+
  contribution (FIy_ValuePacked.rangeModel o s) 49 j.val+
  contribution (FIy_ValuePacked.conservation o s) 82 j.val+
  contribution (FIy_OccupancyMeaning.model (FIy_OccupancyPacked.input s) (FIy_OccupancyPacked.output s)
    (FIy_OccupancyRows.expected p.variant) (FIv_NativeArray.value o.z)) 0 j.val+
  contribution (FIy_PublicDigest.model p o s) 84 j.val+
  contribution (FIy_ScalarPacked.model p o s) 92 j.val

/-- Installed-source coefficient VALUE on unchanged native operands.
Retained Semantic24/literal carrier alignment is still a separate obligation. -/
theorem value (p : Public) (o : Openings) (s : Selectors) (out : Array NQ 24#usize)
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
    (success : pool_v1.pair_forest_semantic_terminal.semantic_packed p o s=ok out) :
    canonical out ∧ decoded out=model p o s := by
  rw [FIy_CoefficientSource.factor] at success
  obtain ⟨a,h_a,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨b,h_b,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨c,h_c,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨d,h_d,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨digest,h_digest,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨e,h_e,success⟩ := FIv_Map.bind_success _ _ _ success
  have zero : canonical (Array.repeat 24#usize field.QM31.ZERO) := by
    intro x hx
    have same : x=field.QM31.ZERO := List.eq_of_mem_replicate hx
    rw [same]
    exact FIv_NativeValue.zero.1
  have v1 := FIx_SchedulePacked.value _ a p o s zero hz hh hl h_a
  have v2 := FIx_PathPacked.value a b o s v1.1 hz hs hh hl h_b
  have v3 := FIy_ValuePacked.value b c o s v2.1 hz hs hx hh hl h_c
  have v4 := FIy_OccupancyPacked.value c d p o s v3.1 hz hh hl h_d
  have vd := FIy_PublicDigest.value p o s digest hz hh hl ha hn hr hc hf hnr hnf h_digest
  have v5 := FIx_PreweightedMeaning.value d e 84#usize digest (FIy_PublicDigest.model p o s) vd.2
    (by decide) (by decide) v4.1 vd.1 h_e
  have v6 := FIy_ScalarPacked.value p o s e out hz hh hl v5.1 hab haw success
  refine ⟨v6.1,?_⟩
  funext j
  rw [v6.2 j,v5.2 j,v4.2 j,v3.2 j,v2.2 j,v1.2 j,FIx_ArrayMeaning.decoded_repeat,FIv_NativeValue.zero.2,zero_add]
  rfl
#print axioms value
end AspisR1.FIy_NativeCoefficients
end
