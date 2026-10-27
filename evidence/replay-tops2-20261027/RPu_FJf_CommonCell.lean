import RPu_FJf_QMArray
import RPu_FJf_CommonIndices
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJf_CommonCell
open Aeneas Aeneas.Std Result ControlFlow AspisR1CurrentWide.Proof
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
open FIo_FieldBridge (NQ qm)

def model (p : Array FIn_WeightsExtract.field.QM31 10#usize) (j : Nat) : OraclePortCheckpointAbiC5.K :=
  FJf_PointCell.point p 2 ⟨j%4,Nat.mod_lt _ (by decide)⟩ *
    FJf_PointCell.point p 3 ⟨j/4%4,Nat.mod_lt _ (by decide)⟩

theorem value (alpha : Array K 10#usize) (z : Array aspis_core.circle.SecureCirclePoint 2#usize)
    (w : FIo_Install.W)
    (hc : FJc_WeightArray.canonical (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha))
    (hw : FIn_WeightsInstall.newWeights .S2 alpha z=ok (.Ok w))
    (iter cursor : FIo_RangeNext.Range) (common next : Array NQ 16#usize)
    (he : iter.end.val=16) (hcanon : FJf_QMArray.canon common)
    (run : FIo_Native.weights.Weights.pair_loop1.body (FIo_Install.toWeights w) iter common=
      ok (.cont (cursor,next))) :
    cursor.end=iter.end ∧ cursor.start.val=iter.start.val+1 ∧ iter.start.val < iter.end.val ∧
    FJf_QMArray.canon next ∧ ∀ j,FJf_QMArray.value next j=
      if iter.start.val=j then model (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha) j
      else FJf_QMArray.value common j := by
  unfold FIo_Native.weights.Weights.pair_loop1.body at run
  obtain ⟨⟨o,cursor'⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none => cases run
  | some j =>
    simp only [lift,bind_tc_ok] at run
    obtain ⟨row,hr,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨digit2,hd2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨q2,hq2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨digit3,hd3,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨q3,hq3,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨prod,hprod,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨updated,hu,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    cases Result.ok.inj run
    have pr := FIo_RangeNext.some_next iter cursor j hn
    have jl : j.val < 16 := by rw [pr.1];omega
    have lowBound : (j &&& 3#usize).val < 4 := by rw [FJf_CommonIndices.low];omega
    have highBound : (Usize.wrapping_shr j 2#u32).val < 4 := by rw [FJf_CommonIndices.high];omega
    have v2 := FJf_InstalledPointCell.value .S2 alpha z w hc hw 2#usize (j &&& 3#usize)
      (by decide) lowBound row digit2 q2 hr hd2 hq2
    have v3 := FJf_InstalledPointCell.value .S2 alpha z w hc hw 3#usize (Usize.wrapping_shr j 2#u32)
      (by decide) highBound row digit3 q3 hr hd3 hq3
    have vp := FIo_QMMulValues.mul q2 q3 prod v2.1 v3.1 hprod
    have vm : decodeQM (qm prod)=model (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha) j.val := by
      rw [vp.2,v2.2,v3.2]
      simp only [model,show (2#usize).val=2 from by decide,show (3#usize).val=3 from by decide,
        FJf_CommonIndices.low,FJf_CommonIndices.high,Nat.mod_eq_of_lt (by omega : j.val/4 < 4)]
    refine ⟨pr.2.1,pr.2.2.1,pr.2.2.2,FJf_QMArray.update_canon common next j prod hcanon vp.1 hu,?_⟩
    intro i
    rw [FJf_QMArray.update common next j prod hu i,vm,pr.1]
    by_cases eq : iter.start.val=i
    · simp only [eq,if_true]
    · simp only [eq,if_false]
#print axioms value
end AspisR1.FJf_CommonCell
end
