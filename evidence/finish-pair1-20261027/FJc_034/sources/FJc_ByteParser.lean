import FJc_LimbParser
set_option autoImplicit false
namespace AspisR1.FJc_ByteParser
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE)
open FJc_ByteCarrier (toRecord)
/-- Success of the SAME native byte parser transports to the retained strict
record parser. Only the outer fixed 32 reads are unfolded. -/
theorem source (bytes : Slice U8) (out : NE)
    (run : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes bytes=ok (some out)) :
    AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes bytes=ok (some (toRecord out)) := by
  unfold FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes at run
  dsimp only at run
  simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.BYTE_LEN] at run
  split at run
  · cases run
  rename_i no
  have hlen : Slice.len bytes=32#usize := by simpa using no
  simp only [lift,bind_tc_ok] at run
  obtain ⟨b0,h0,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b1,h1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b2,h2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b3,h3,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b4,h4,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b5,h5,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b6,h6,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b7,h7,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b8,h8,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b9,h9,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b10,h10,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b11,h11,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b12,h12,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b13,h13,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b14,h14,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b15,h15,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b16,h16,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b17,h17,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b18,h18,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b19,h19,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b20,h20,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b21,h21,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b22,h22,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b23,h23,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b24,h24,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b25,h25,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b26,h26,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b27,h27,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b28,h28,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b29,h29,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b30,h30,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b31,h31,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have target := FJc_LimbParser.source _ out run
  simpa only [AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes,
    AspisR1RecordParser.field.wide_exact.WideExact.BYTE_LEN,hlen,
    bne_self_eq_false,Bool.false_eq_true,↓reduceIte,lift,bind_tc_ok,
    h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31] using target
#print axioms source
end AspisR1.FJc_ByteParser
