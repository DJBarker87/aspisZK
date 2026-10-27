import FIo_FromLimbs
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIo_FromBytes
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE)

theorem canonical (bytes : Slice U8) (z : NE)
    (run : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes bytes=ok (some z)) :
    FIo_WideValues.Canon z := by
  unfold FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes at run
  split at run
  · cases run
  obtain ⟨b0_0,hb0_0,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b0_1,hb0_1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b0_2,hb0_2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b0_3,hb0_3,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  simp only [lift,bind_tc_ok] at run
  obtain ⟨b1_0,hb1_0,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b1_1,hb1_1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b1_2,hb1_2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b1_3,hb1_3,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  simp only [lift,bind_tc_ok] at run
  obtain ⟨b2_0,hb2_0,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b2_1,hb2_1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b2_2,hb2_2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b2_3,hb2_3,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  simp only [lift,bind_tc_ok] at run
  obtain ⟨b3_0,hb3_0,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b3_1,hb3_1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b3_2,hb3_2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b3_3,hb3_3,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  simp only [lift,bind_tc_ok] at run
  obtain ⟨b4_0,hb4_0,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b4_1,hb4_1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b4_2,hb4_2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b4_3,hb4_3,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  simp only [lift,bind_tc_ok] at run
  obtain ⟨b5_0,hb5_0,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b5_1,hb5_1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b5_2,hb5_2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b5_3,hb5_3,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  simp only [lift,bind_tc_ok] at run
  obtain ⟨b6_0,hb6_0,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b6_1,hb6_1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b6_2,hb6_2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b6_3,hb6_3,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  simp only [lift,bind_tc_ok] at run
  obtain ⟨b7_0,hb7_0,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b7_1,hb7_1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b7_2,hb7_2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b7_3,hb7_3,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  simp only [lift,bind_tc_ok] at run
  exact FIo_FromLimbs.canonical _ z run

#print axioms canonical
end AspisR1.FIo_FromBytes
end
