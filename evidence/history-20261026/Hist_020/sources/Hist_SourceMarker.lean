import CheckpointBytes5Writer
import Hist_Store
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hist_SourceMarker
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open CheckpointBytes5Effect CheckpointBytes5Writer
open Hist_Store

theorem source_head (p : Prepared) (a : Accumulator) (hp hu : Digest) :
    (CheckpointBytesDecodeC5.sourceBody p a hp hu)[0]? = some (82 : AspisV8R19.DuplexFrames.Byte) := by
  simp only [CheckpointBytesDecodeC5.sourceBody,List.getElem?_ofFn]
  rfl

theorem finish_initialized (p : Prepared) (a : Accumulator) (hp hu hc : Digest) :
    Initialized (finish p a hp hu hc) := by
  constructor
  · simp only [finish,List.length_append,List.length_map,
      CheckpointBytesDecodeC5.sourceBody,List.length_ofFn,hc.property]
    omega
  · have head := source_head p a hp hu
    have len : (CheckpointBytesDecodeC5.sourceBody p a hp hu).length = 1736 := by
      simp only [CheckpointBytesDecodeC5.sourceBody,List.length_ofFn]
    have pos : 0 < (CheckpointBytesDecodeC5.sourceBody p a hp hu).length := by omega
    rw [List.getElem?_eq_getElem pos] at head
    have raw := Option.some.inj head
    simp [finish,Slice.index_usize,List.getElem_append_left,List.getElem_map,len,raw,u8]

#print axioms source_head
#print axioms finish_initialized
end AspisR1.Hist_SourceMarker
end
