import AspisV8R19.R205AbsorbHashCall

/-! Transport the arbitrary-hash absorb call expression to the current selected
transcript; record the exact flattened address for either packing branch. -/
set_option autoImplicit false
namespace AspisV8R19.R206CurrentAbsorbHashCall
open Aeneas Aeneas.Std Result
open AspisR156FullFreeze.aspis_core
open R205AbsorbHashCall
open R167TranscriptPrimitiveExecution (toR137 fromR137)

 theorem short_execution (t : transcript.Transcript) (label : U8) (data : Slice U8)
    (short : data.len ≤ transcript.Transcript.absorb.PACKED_ABSORB_BYTES.wrapping_sub
      34#usize) :
    transcript.Transcript.absorb t label data = (do
      let next ← t.hash (packedMessage t.state label data (by
        change data.val.length ≤ _ at short
        have hlim :
            (transcript.Transcript.absorb.PACKED_ABSORB_BYTES.wrapping_sub
              34#usize).val = 158 := by
          simpa only [transcript.Transcript.absorb.PACKED_ABSORB_BYTES,
            AspisR137Transcript.transcript.Transcript.absorb.PACKED_ABSORB_BYTES]
            using R137TranscriptPrimitiveBridge.packed_payload_limit
        rwa [hlim] at short))
      ok {t with state := next}) := by
  have h : data.len ≤
      AspisR137Transcript.transcript.Transcript.absorb.PACKED_ABSORB_BYTES.wrapping_sub
        34#usize := by
    simpa only [transcript.Transcript.absorb.PACKED_ABSORB_BYTES,
      AspisR137Transcript.transcript.Transcript.absorb.PACKED_ABSORB_BYTES] using short
  rw [R167TranscriptPrimitiveExecution.absorb_map, R205AbsorbHashCall.short_execution _ _ _ h]
  cases t
  simp only [toR137,fromR137,bind_assoc_eq,bind_tc_ok]

 theorem long_execution (t : transcript.Transcript) (label : U8) (data : Slice U8)
    (long : ¬data.len ≤ transcript.Transcript.absorb.PACKED_ABSORB_BYTES.wrapping_sub
      34#usize) :
    transcript.Transcript.absorb t label data = (do
      let next ← t.hash (multipartMessage t.state label data)
      ok {t with state := next}) := by
  have h : ¬data.len ≤
      AspisR137Transcript.transcript.Transcript.absorb.PACKED_ABSORB_BYTES.wrapping_sub
        34#usize := by
    simpa only [transcript.Transcript.absorb.PACKED_ABSORB_BYTES,
      AspisR137Transcript.transcript.Transcript.absorb.PACKED_ABSORB_BYTES] using long
  rw [R167TranscriptPrimitiveExecution.absorb_map, R205AbsorbHashCall.long_execution _ _ _ h]
  cases t
  simp only [toR137,fromR137,bind_assoc_eq,bind_tc_ok]

 theorem packed_address (state : Array U8 32#usize) (label : U8) (data : Slice U8)
    (hd : data.val.length ≤ 158) :
    SqueezeOracleBridge.flatten (packedMessage state label data hd) =
      DuplexFrames.absorb (state.val.map SqueezeOracleBridge.decodeByte)
        (SqueezeOracleBridge.decodeByte label)
        (R137TranscriptPrimitiveBridge.decodedSlice data) := by
  simp [SqueezeOracleBridge.flatten,packedMessage,packed,Array.to_slice,Array.make,
    DuplexFrames.absorb,R137TranscriptPrimitiveBridge.decodedSlice]
  rfl

 theorem multipart_address (state : Array U8 32#usize) (label : U8) (data : Slice U8) :
    SqueezeOracleBridge.flatten (multipartMessage state label data) =
      DuplexFrames.absorb (state.val.map SqueezeOracleBridge.decodeByte)
        (SqueezeOracleBridge.decodeByte label)
        (R137TranscriptPrimitiveBridge.decodedSlice data) := by
  simp [SqueezeOracleBridge.flatten,multipartMessage,Array.to_slice,Array.make,
    DuplexFrames.absorb,R137TranscriptPrimitiveBridge.decodedSlice,List.append_assoc]
  rfl

#print axioms short_execution
#print axioms long_execution
#print axioms packed_address
#print axioms multipart_address
end AspisV8R19.R206CurrentAbsorbHashCall
