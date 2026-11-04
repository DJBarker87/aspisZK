import NGK_COMBINED_IMPORT
import NGC_KNE_Writer
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGR_HISTORY
open Aeneas Aeneas.Std Result
open CheckpointBytes5Writer CheckpointBytes5Effect

/-- The packet's actual deterministic returned value, with no extra witness
record or output-equality law. The three digest replies are producer inputs. -/
abbrev checkpoint (prepared : Prepared) (accumulator : Accumulator)
    (domain : NGC_KNE_Caller.WriterDomain prepared accumulator)
    (hp hu hc : Digest) : alloc.vec.Vec U8 :=
  NGC_KNE_Writer.returned prepared accumulator domain hp hu hc

theorem checkpoint_length (prepared : Prepared) (accumulator : Accumulator)
    (domain : NGC_KNE_Caller.WriterDomain prepared accumulator)
    (hp hu hc : Digest) :
    (checkpoint prepared accumulator domain hp hu hc).val.length = 1768 := by
  change (NGC_KNE_Writer.returned prepared accumulator domain hp hu hc).val.length = _
  rw [NGC_KNE_Writer.returned_eq, NGC_LPm_CheckpointProgram.returned_eq]
  simp only [finish, List.length_append, List.length_map,
    CheckpointBytesDecodeC5.sourceBody, List.length_ofFn, hc.property]
  rfl

#print axioms checkpoint_length
end AspisR1.NGR_HISTORY
end
