import FJc_PartNames
import Port3_PushFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJc_Constructor
open Aeneas Aeneas.Std Result
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
/-- Inversion of the installed constructor, keeping its original input arrays.
No independently selected points or final factors are supplied as hypotheses. -/
theorem source (v : transport.Variant) (alpha : Array K 10#usize)
    (z : Array aspis_core.circle.SecureCirclePoint 2#usize) (w : FIo_Install.W)
    (run : FIn_WeightsInstall.newWeights v alpha z=ok (.Ok w)) :
    FIn_WeightsExtract.weights_new (FIn_WeightsInstall.variant v)
      (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha)
      (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toPoint z)=ok (.Ok w) := by
  unfold FIn_WeightsInstall.newWeights at run
  cases h : FIn_WeightsExtract.weights_new (FIn_WeightsInstall.variant v)
      (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha)
      (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toPoint z) with
  | fail e => simp only [h,bind_tc_fail] at run; cases run
  | div => simp only [h,bind_tc_div] at run; cases run
  | ok r =>
    simp only [h,bind_tc_ok] at run
    cases r with
    | Err e => cases e; cases run
    | Ok x => cases core.result.Result.Ok.inj (Result.ok.inj run); rfl

/-- Successful construction exposes its SAME points, factors and two extra
coordinates. This only unfolds the straight-line outer constructor. -/
theorem parts (v : FIn_WeightsExtract.FInVariant)
    (alpha : Array FIn_WeightsExtract.field.QM31 10#usize)
    (z : Array FIn_WeightsExtract.circle.SecureCirclePoint 2#usize)
    (w : FIn_WeightsExtract.Weights)
    (run : FIn_WeightsExtract.weights_new v alpha z=ok (.Ok w)) :
    ∃ points a8 a9 factors1 factors2,
      FIn_WeightsExtract.state_only_prefix.r0.statement_points alpha=ok points ∧
      Array.index_usize alpha 8#usize=ok a8 ∧
      Array.index_usize alpha 9#usize=ok a9 ∧
      FIn_WeightsExtract.weights_new_loop0 {start:=0#usize,«end»:=3#usize} points
        (Array.repeat 5#usize (Array.repeat 5#usize
          (Array.repeat 4#usize FIn_WeightsExtract.field.QM31.ZERO)))=ok factors1 ∧
      FIn_WeightsExtract.weights_new_loop1 {start:=0#usize,«end»:=2#usize} z factors1=ok factors2 ∧
      w=⟨v,factors2,points,Array.make 2#usize [a8,a9]⟩ := by
  unfold FIn_WeightsExtract.weights_new at run
  obtain ⟨points,hpoints,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨a8,ha8,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨a9,ha9,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨factors1,hf1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨factors2,hf2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  simp only [FIn_WeightsExtract.Weights.box_from_parts,bind_tc_ok] at run
  have same := core.result.Result.Ok.inj (Result.ok.inj run)
  exact ⟨points,a8,a9,factors1,factors2,hpoints,ha8,ha9,hf1,hf2,same.symm⟩
#print axioms source
#print axioms parts
end AspisR1.FJc_Constructor
end
