import AspisV8R19.SqueezeSourceExecution
import AspisV8R19.SourceDuplexStep

/-! Exact representation bridge under an explicitly constructed total hashv
adapter. No independence, freshness, SHA ideality, or concrete-backend law. -/
set_option autoImplicit false
namespace AspisV8R19.SqueezeOracleBridge
open Aeneas Aeneas.Std Result AspisR72Sampler
open DuplexFrames SourceDuplexStep SqueezeSourceExecution

def encodeByte (b : DuplexFrames.Byte) : U8 := UScalar.ofNatCore b.val b.isLt
def decodeByte (b : U8) : DuplexFrames.Byte := ⟨b.val,b.bv.isLt⟩
def encodeState (s : State) : Array U8 32#usize :=
  ⟨(bytes s).map encodeByte,by simp [bytes]⟩
def decodeState (s : Array U8 32#usize) : State :=
  fun i => decodeByte (s.val[i.val]'(by have hs : s.val.length=32 := s.property; omega))
def flatten (input : Slice (Slice U8)) : Bytes :=
  (input.val.flatMap (fun part => part.val)).map decodeByte
def hashAdapter (H : Bytes → State) (input : Slice (Slice U8)) : Result (Array U8 32#usize) :=
  .ok (encodeState (H (flatten input)))
def transcriptFor (H : Bytes → State) (s : State) : transcript.Transcript :=
  ⟨encodeState s,hashAdapter H⟩

theorem byte_roundtrip (b : DuplexFrames.Byte) : decodeByte (encodeByte b) = b := by
  apply Fin.ext; rfl
theorem word_roundtrip (b : U8) : encodeByte (decodeByte b) = b := by
  apply UScalar.eq_of_val_eq; rfl
theorem state_roundtrip (s : State) : decodeState (encodeState s) = s := by
  funext i
  simp only [decodeState,encodeState,bytes,List.getElem_map,List.getElem_ofFn,byte_roundtrip]
theorem array_roundtrip (s : Array U8 32#usize) : encodeState (decodeState s) = s := by
  apply Subtype.ext
  apply List.ext_getElem
  · simp [encodeState,bytes,s.property]
  · intro i hi hj
    simp only [encodeState,bytes,List.getElem_map,List.getElem_ofFn,decodeState,word_roundtrip]
theorem frame_address (s : State) (tag : DuplexFrames.Byte) :
    flatten (message (encodeState s) (encodeByte tag)) = bytes s ++ [tag] := by
  simp [flatten,message,frame,Array.to_slice,Array.make,encodeState,
    List.map_map,Function.comp_def,byte_roundtrip]
theorem squeeze_address (s : State) :
    flatten (message (encodeState s) 1#u8) = DuplexFrames.squeeze (bytes s) := by
  exact frame_address s 1
theorem advance_address (s : State) :
    flatten (message (encodeState s) 2#u8) = DuplexFrames.advance (bytes s) := by
  exact frame_address s 2

theorem source_step (H : Bytes → State) (s : State) :
    transcript.Transcript.squeeze_block (transcriptFor H s) =
      .ok (encodeState (step H s).1,transcriptFor H (step H s).2) := by
  rw [SqueezeSourceExecution.execution]
  simp only [transcriptFor,hashAdapter,squeeze_address,advance_address,bind_tc_ok,step]
theorem decoded_step (H : Bytes → State) (s : State) :
    (do
      let (out,next) ← transcript.Transcript.squeeze_block (transcriptFor H s)
      ok (decodeState out,decodeState next.state)) = .ok (step H s) := by
  rw [source_step]
  simp only [bind_tc_ok,transcriptFor,state_roundtrip]
theorem addresses_match (H : Bytes → State) (s : State) :
    [(flatten (message (encodeState s) 1#u8),(step H s).1),
     (flatten (message (encodeState s) 2#u8),(step H s).2)] = calls H s := by
  simp only [squeeze_address,advance_address,calls]

#print axioms byte_roundtrip
#print axioms word_roundtrip
#print axioms state_roundtrip
#print axioms array_roundtrip
#print axioms frame_address
#print axioms squeeze_address
#print axioms advance_address
#print axioms source_step
#print axioms decoded_step
#print axioms addresses_match
end AspisV8R19.SqueezeOracleBridge
