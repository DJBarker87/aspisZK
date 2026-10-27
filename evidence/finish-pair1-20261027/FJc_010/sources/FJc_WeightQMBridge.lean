import FJc_WeightByR
set_option autoImplicit false
namespace AspisR1.FJc_WeightQMBridge
open Aeneas Aeneas.Std Result
open FIo_Install (toQ)
abbrev SQ := FIn_WeightsExtract.field.QM31

theorem add (x y z : SQ) (run : FIn_WeightsExtract.field.QM31.add x y=ok z) :
    FIo_Native.aspis_core.field.QM31.add (toQ x) (toQ y)=ok (toQ z) := by
  unfold FIn_WeightsExtract.field.QM31.add at run
  obtain ⟨a,ha,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b,hb,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have ha := FJc_WeightCMBridge.add _ _ _ ha
  have hb := FJc_WeightCMBridge.add _ _ _ hb
  cases Result.ok.inj run
  unfold FIo_Native.aspis_core.field.QM31.add
  change (do let a ← FIo_Native.aspis_core.field.CM31.add _ _
             let b ← FIo_Native.aspis_core.field.CM31.add _ _
             ok (⟨a,b⟩ : FIo_Install.NQ))=ok _
  simp only [toQ,FJc_WeightCMBridge.toC] at ha hb ⊢
  rw [ha]; simp only [bind_tc_ok]; rw [hb]; rfl

theorem sub (x y z : SQ) (run : FIn_WeightsExtract.field.QM31.sub x y=ok z) :
    FIo_Native.aspis_core.field.QM31.sub (toQ x) (toQ y)=ok (toQ z) := by
  unfold FIn_WeightsExtract.field.QM31.sub at run
  obtain ⟨a,ha,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b,hb,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have ha := FJc_WeightCMBridge.sub _ _ _ ha
  have hb := FJc_WeightCMBridge.sub _ _ _ hb
  cases Result.ok.inj run
  unfold FIo_Native.aspis_core.field.QM31.sub
  change (do let a ← FIo_Native.aspis_core.field.CM31.sub _ _
             let b ← FIo_Native.aspis_core.field.CM31.sub _ _
             ok (⟨a,b⟩ : FIo_Install.NQ))=ok _
  simp only [toQ,FJc_WeightCMBridge.toC] at ha hb ⊢
  rw [ha]; simp only [bind_tc_ok]; rw [hb]; rfl
#print axioms add
#print axioms sub
end AspisR1.FJc_WeightQMBridge
