import AspisR136BeforeOod.Funs
import AspisV8R19.R137TranscriptPrimitiveBridge

/-! Exact new/absorb correspondence for the transcript operations imported by
the selected R136 callback.  Both packed and long absorb paths are retained.
This is a deterministic source bridge, not a distribution or security claim. -/
set_option autoImplicit false
namespace AspisV8R19.R141BeforeOodPrimitiveBridge

open Aeneas Aeneas.Std Result
open AspisV8R19 DuplexFrames SourceDuplexStep
open R137TranscriptPrimitiveBridge

theorem new_exact (H : Bytes → State) :
    AspisR136BeforeOod.aspis_core.transcript.Transcript.new
        (SqueezeOracleBridge.hashAdapter H) =
      .ok (transcriptFor H zeroState) := by
  unfold AspisR136BeforeOod.aspis_core.transcript.Transcript.new
  exact new_execution H

theorem absorb_exact (H : Bytes → State) (s : State)
    (label : U8) (data : Slice U8) :
    AspisR136BeforeOod.aspis_core.transcript.Transcript.absorb
        (transcriptFor H s) label data =
      .ok (transcriptFor H
        (H (DuplexFrames.absorb (SourceDuplexStep.bytes s)
          (SqueezeOracleBridge.decodeByte label) (decodedSlice data)))) := by
  unfold AspisR136BeforeOod.aspis_core.transcript.Transcript.absorb
  by_cases h : data.len ≤
      AspisR137Transcript.transcript.Transcript.absorb.PACKED_ABSORB_BYTES.wrapping_sub
        34#usize
  · exact short_absorb_execution H s label data h
  · exact long_absorb_execution H s label data h

#print axioms new_exact
#print axioms absorb_exact

end AspisV8R19.R141BeforeOodPrimitiveBridge
