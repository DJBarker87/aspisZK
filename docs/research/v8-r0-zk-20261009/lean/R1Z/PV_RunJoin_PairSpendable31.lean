import R1Z.PV_RunJoin_RuntimeRejections30
import R1Z.PV_RunJoin_OuterABI30
import R1Z.PV_RunJoin_WitnessViews31
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PairSpendable31
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_RunJoin_OuterABI30 PV_Src_NativeInput PV_RunJoin_SemanticChange30

theorem selected (p : AspisBuilderAdmissionSource.pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1)
    (b : Bool) (h : p.require_selected_spendable b = ok (.Ok ())) :
    b=true → p.second_occupied = 1#u32 := by
  intro hb
  subst b
  have hv := BuilderAdmissionCommon.selected_validates p true h
  unfold AspisBuilderAdmissionSource.pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1.require_selected_spendable at h
  rw [hv] at h
  simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,↓reduceIte] at h
  pv_peel h with mismatch hm
  obtain ⟨hne,_⟩ := BuilderAdmissionRanges.error_then h
  have hf : mismatch=false := Bool.eq_false_iff.mpr hne
  subst mismatch
  rw [PV_RunJoin_RuntimePrimitives30.word_ne] at hm
  simpa only [AspisBuilderAdmissionSource.aspis_core.field.M31.ONE,
    Result.ok.injEq,decide_eq_false_iff_not,not_not] using hm
#print axioms selected

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

theorem semantic (i : Input)
    (h : (leafToAdmission (leafFromForest i.witness.pair.pair_leaf)).require_selected_spendable
      i.witness.pair.selected_second = ok (.Ok ())) :
    (witness (K := K) i).pair.SelectedSlotIsSpendable ((witness (K := K) i).path 0).1 := by
  unfold AspisPool.V7PairLeafOccupancy.PairLeaf.SelectedSlotIsSpendable
    AspisPool.V7PairLeafOccupancy.PairLeaf.selectedOccupied
  rw [PV_RunJoin_WitnessViews31.first_direction,PV_RunJoin_WitnessViews31.pair_occupied]
  cases hb : i.witness.pair.selected_second
  · rfl
  · have ho := selected _ _ h hb
    change i.witness.pair.pair_leaf.second_occupied = 1#u32 at ho
    rw [ho]
    simp only [↓reduceIte,liftU,UScalar.ofNatCore_val_eq,Nat.cast_one]
#print axioms semantic
end R1Z.PV_RunJoin_PairSpendable31
