import CheckpointBytes5Writer
import Hist_InitialZero
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hist_SourceMarker
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open CheckpointBytes5Effect CheckpointBytes5Writer

/-- A tiny executable marker suffices for write-once protection. -/
def Initialized (s : Slice U8) : Prop :=
  0 < s.val.length ∧ Slice.index_usize s 0#usize = ok (82#u8)

theorem source_head (p : Prepared) (a : Accumulator) (hp hu : Digest) :
    (CheckpointBytesDecodeC5.sourceBody p a hp hu)[0]? = some (82 : Byte) := by
  simp only [CheckpointBytesDecodeC5.sourceBody,List.getElem?_ofFn]
  rfl

theorem finish_initialized (p : Prepared) (a : Accumulator) (hp hu hc : Digest) :
    Initialized (finish p a hp hu hc) := by
  constructor
  · simp only [finish,List.length_append,List.length_map,
      CheckpointBytesDecodeC5.sourceBody,List.length_ofFn,hc.property]
    omega
  · have head := source_head p a hp hu
    simp only [Initialized,finish,Slice.index_usize]
    simp [List.getElem?_append,head]

#print axioms source_head
#print axioms finish_initialized
end AspisR1.Hist_SourceMarker
end
