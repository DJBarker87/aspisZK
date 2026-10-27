import RPt_FJc_WeightQMBridge
set_option autoImplicit false
namespace AspisR1.FJc_WeightQMMul
open Aeneas Aeneas.Std Result
open FIo_Install (toQ)
open FJc_WeightQMBridge (SQ)
theorem mul (x y z : SQ) (run : FIn_WeightsExtract.field.QM31.mul x y=ok z) :
    FIo_Native.aspis_core.field.QM31.mul (toQ x) (toQ y)=ok (toQ z) := by
  unfold FIn_WeightsExtract.field.QM31.mul at run
  obtain ⟨a,ha,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b,hb,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨c,hc,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨d,hd,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨e,he,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨f,hf,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨g,hg,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨h,hh,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨i,hi,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have ha := FJc_WeightCMMul.mul _ _ _ ha
  have hb := FJc_WeightCMMul.mul _ _ _ hb
  have hc := FJc_WeightCMBridge.add _ _ _ hc
  have hd := FJc_WeightCMBridge.add _ _ _ hd
  have he := FJc_WeightCMMul.mul _ _ _ he
  have hf := FJc_WeightByR.value _ _ hf
  have hg := FJc_WeightCMBridge.add _ _ _ hg
  have hh := FJc_WeightCMBridge.sub _ _ _ hh
  have hi := FJc_WeightCMBridge.sub _ _ _ hi
  cases Result.ok.inj run
  unfold FIo_Native.aspis_core.field.QM31.mul
  simp only [toQ]
  change (do let a ← FIo_Native.aspis_core.field.CM31.mul _ _
             let b ← FIo_Native.aspis_core.field.CM31.mul _ _
             let c ← FIo_Native.aspis_core.field.CM31.add _ _
             let d ← FIo_Native.aspis_core.field.CM31.add _ _
             let e ← FIo_Native.aspis_core.field.CM31.mul c d
             let f ← FIo_Native.aspis_core.field.mul_by_r b
             let g ← FIo_Native.aspis_core.field.CM31.add a f
             let h ← FIo_Native.aspis_core.field.CM31.sub e a
             let i ← FIo_Native.aspis_core.field.CM31.sub h b
             ok (⟨g,i⟩ : FIo_Install.NQ))=ok _
  simp only [toQ,FJc_WeightCMBridge.toC] at ha hb hc hd he hf hg hh hi ⊢
  rw [ha]; simp only [bind_tc_ok]
  rw [hb]; simp only [bind_tc_ok]
  rw [hc]; simp only [bind_tc_ok]
  rw [hd]; simp only [bind_tc_ok]
  rw [he]; simp only [bind_tc_ok]
  rw [hf]; simp only [bind_tc_ok]
  rw [hg]; simp only [bind_tc_ok]
  rw [hh]; simp only [bind_tc_ok]
  rw [hi]; rfl
#print axioms mul
end AspisR1.FJc_WeightQMMul
