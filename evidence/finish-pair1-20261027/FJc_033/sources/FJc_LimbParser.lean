import FJc_ByteCarrier
set_option autoImplicit false
namespace AspisR1.FJc_LimbParser
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE)
open FJc_ByteCarrier (toRecord)
/-- The SAME eight limbs and ordered canonical guards in the two retained
source parser carriers, success-conditioned. -/
theorem source (limbs : Array U32 8#usize) (out : NE)
    (run : FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs limbs=ok (some out)) :
    AspisR1RecordParser.field.wide_exact.WideExact.from_limbs limbs=ok (some (toRecord out)) := by
  unfold FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs at run
  obtain ⟨a0,h0,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  split at run
  · cases run
  rename_i c0
  obtain ⟨a1,h1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  split at run
  · cases run
  rename_i c1
  obtain ⟨a2,h2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  split at run
  · cases run
  rename_i c2
  obtain ⟨a3,h3,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  split at run
  · cases run
  rename_i c3
  obtain ⟨a4,h4,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  split at run
  · cases run
  rename_i c4
  obtain ⟨a5,h5,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  split at run
  · cases run
  rename_i c5
  obtain ⟨a6,h6,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  split at run
  · cases run
  rename_i c6
  obtain ⟨a7,h7,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  split at run
  · cases run
  rename_i c7
  cases Option.some.inj (Result.ok.inj run)
  simp only [AspisR1RecordParser.field.wide_exact.WideExact.from_limbs,
    AspisR1RecordParser.field.P,h0,h1,h2,h3,h4,h5,h6,h7,bind_tc_ok]
  simp only [FIo_Native.aspis_core.field.P] at c0 c1 c2 c3 c4 c5 c6 c7
  simp only [c0,c1,c2,c3,c4,c5,c6,c7,↓reduceIte,toRecord]
#print axioms source
end AspisR1.FJc_LimbParser
