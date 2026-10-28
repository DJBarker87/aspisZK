import KNE_Model
import KNE_Caller
set_option autoImplicit false
noncomputable section
namespace AspisR1.KNE_Schedule
open Aeneas Aeneas.Std
open CheckpointBytes5Effect CheckpointBytes5Writer CheckpointBytesBlocks CheckpointBytesBody CheckpointBytesDigest
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open KNE_Model KNE_Caller

def writerEmissions (f : Fields) (hp hu hc : State) : List (String × Bytes) :=
  bodyEmissions f hp hu ++ [("checksum",bytes hc)]

theorem writer_shape (f : Fields) (hp hu hc : State) :
    shape (writerEmissions f hp hu hc) = KND_Schedule.emissions := by
  change shape (bodyEmissions f hp hu) ++ [("checksum",(bytes hc).length)] = _
  rw [bodyEmissions_shape]
  rfl

-- Source-profile final_len: transport.rs uses 1024 >> (2*folds), folds(S2)=2.
def sourceFinalLen (v : OraclePortCkptAbi2Extracted.aspis_r1_cost_probe.transport.CheckpointAbi2Variant) : Nat :=
  1024 >>> (2 * (match v with | .S1 => 1 | _ => 2))

theorem caller_final_len (p : Prepared) (a : Accumulator) (domain : WriterDomain p a) :
    sourceFinalLen p.variant = 64 := by
  rw [domain.variant]
  decide

def derivedSchedule (p : Prepared) (a : Accumulator) (domain : WriterDomain p a)
    (hp hu hc : Digest) : List KND_Schedule.Step :=
  KND_Schedule.annotate 0 (shape (writerEmissions (fields p a domain.size domain.queriesBound)
    (stateOf hp) (stateOf hu) (stateOf hc)))

theorem derived_schedule (p : Prepared) (a : Accumulator) (domain : WriterDomain p a)
    (hp hu hc : Digest) :
    derivedSchedule p a domain hp hu hc = KND_Schedule.schedule := by
  unfold derivedSchedule
  rw [writer_shape]
  rfl

theorem native_body_decomposition (p : Prepared) (a : Accumulator) (domain : WriterDomain p a)
    (hp hu : Digest) :
    payload (bodyEmissions (fields p a domain.size domain.queriesBound) (stateOf hp) (stateOf hu)) =
      LPm_CheckpointBody.nativeBody p a domain.size domain.queriesBound hp hu :=
  bodyEmissions_payload _ _ _

theorem returned_decomposition (p : Prepared) (a : Accumulator) (domain : WriterDomain p a)
    (hp hu hc : Digest) :
    payload (writerEmissions (fields p a domain.size domain.queriesBound)
      (stateOf hp) (stateOf hu) (stateOf hc)) =
      MultiproofConeCanonical.bytesOf
        (LPm_CheckpointProgram.returned p a domain.size domain.queriesBound
          domain.canonical domain.next hp hu hc).val := by
  rw [LPm_CheckpointProgram.returned_eq,finish_bytes]
  have split (f : Fields) (hp hu hc : State) :
      payload (writerEmissions f hp hu hc) = payload (bodyEmissions f hp hu) ++ bytes hc := by
    simp only [payload,writerEmissions,List.map_append,List.map_cons,List.map_nil,
      List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  rw [split]
  rw [native_body_decomposition p a domain hp hu,LPm_CheckpointBody.source_body p a domain.size
    domain.queriesBound domain.canonical domain.next]

#print axioms writer_shape
#print axioms caller_final_len
#print axioms derived_schedule
#print axioms native_body_decomposition
#print axioms returned_decomposition
end AspisR1.KNE_Schedule
end
