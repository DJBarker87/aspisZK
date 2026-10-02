import AspisV8R19.R206CurrentAbsorbHashCall

/-! Current source primitives under one fallible flattened-byte oracle.
This is value/error/divergence correspondence, not whole callback trace equality
or identification of the concrete hash backend with a random oracle. -/
set_option autoImplicit false
namespace AspisV8R19.R216ResultOraclePrimitives
open Aeneas Aeneas.Std Result
open AspisR156FullFreeze.aspis_core
open DuplexFrames SourceDuplexStep SqueezeOracleBridge

/-- The same H serves every framed address; its failures are retained. -/
def hashAdapter (H : Bytes → Result State) (input : Slice (Slice U8)) :
    Result (Array U8 32#usize) := do
  let reply ← H (flatten input)
  ok (encodeState reply)

def transcriptFor (H : Bytes → Result State) (s : State) : transcript.Transcript :=
  ⟨encodeState s, hashAdapter H⟩

def squeezeStep (H : Bytes → Result State) (s : State) : Result (State × State) := do
  let out ← H (DuplexFrames.squeeze (bytes s))
  let next ← H (DuplexFrames.advance (bytes s))
  ok (out,next)

def absorbStep (H : Bytes → Result State) (s : State) (label : DuplexFrames.Byte)
    (data : Bytes) : Result State := H (DuplexFrames.absorb (bytes s) label data)

theorem squeeze_execution (H : Bytes → Result State) (s : State) :
    transcript.Transcript.squeeze_block (transcriptFor H s) = (do
      let (out,next) ← squeezeStep H s
      ok (encodeState out,transcriptFor H next)) := by
  rw [R167TranscriptPrimitiveExecution.r156_execution]
  simp only [transcriptFor,hashAdapter,squeezeStep,bind_assoc_eq,bind_tc_ok]
  have hm : R147QuerySqueezeBridge.message = SqueezeSourceExecution.message := rfl
  rw [hm,squeeze_address,advance_address]

theorem absorb_execution (H : Bytes → Result State) (s : State)
    (label : U8) (data : Slice U8) :
    transcript.Transcript.absorb (transcriptFor H s) label data = (do
      let next ← absorbStep H s (decodeByte label)
        (R137TranscriptPrimitiveBridge.decodedSlice data)
      ok (transcriptFor H next)) := by
  by_cases h : data.len ≤
      transcript.Transcript.absorb.PACKED_ABSORB_BYTES.wrapping_sub 34#usize
  · rw [R206CurrentAbsorbHashCall.short_execution _ _ _ h]
    simp only [transcriptFor,hashAdapter,bind_assoc_eq,bind_tc_ok,
      R206CurrentAbsorbHashCall.packed_address,absorbStep]
    simp [encodeState,List.map_map,Function.comp_def,byte_roundtrip]
  · rw [R206CurrentAbsorbHashCall.long_execution _ _ _ h]
    simp only [transcriptFor,hashAdapter,bind_assoc_eq,bind_tc_ok,
      R206CurrentAbsorbHashCall.multipart_address,absorbStep]
    simp [encodeState,List.map_map,Function.comp_def,byte_roundtrip]

#print axioms squeeze_execution
#print axioms absorb_execution
end AspisV8R19.R216ResultOraclePrimitives
