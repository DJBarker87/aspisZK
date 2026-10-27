import BEl_PartialRecorder
import BEj_ReifiedBatch
import BEj_LocalExport
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEl_ReferenceObservation
open Aeneas Aeneas.Std Result SdkC_Source

/-- Operational reference observer: pending entries are created before reads,
returned entries after replies, and the ambient stop labels a final pending
attempt. The control is the existing fixed P6 source lowering. Correspondence
of the entire owned Rust reference to this lowering is still a separate gate;
this definition does not identify the physical native wrapper's recorder. -/
def native {S : Type} (call : Parts → S → Result Digest × S)
    (hashv : Parts → Result Digest) (input : BEj_ReifiedBatch.Input) (slot : Fin 2)
    (state : S) (before : Log) :=
  BEl_PartialRecorder.observation (BEl_PartialRecorder.run call
    (BEj_ReifiedBatch.nativeCode hashv input slot) state (BEl_Recorder.completed before))

/-- BothSlots for the explicit operational REFERENCE, including pending failed
attempts. This is not the missing physical native-cut association theorem. -/
theorem observation {S : Type} (call : Parts → S → Result Digest × S)
    (hashv : Parts → Result Digest) :
    BEh_Scope.BothSlots (fun (_ : BEj_ReifiedBatch.Input) (_ : Fin 2) (_ : S) => True)
      (native call hashv)
      (fun input slot state before => BEf_Carrier.run call
        (BEj_ReifiedBatch.sourceCode hashv input slot) state before) := by
  intro input slot state before _
  unfold native
  rw [BEl_PartialRecorder.correspondence,BEj_ReifiedBatch.programs]
  exact BEh_Scope.reflexive _

/-- Exact reference recorder cut exported without assuming its local law.
The returned/failed attempt log is not replaced by a fresh independent log. -/
theorem export_cut {S : Type} (call : Parts → S → Result Digest × S)
    (hashv : Parts → Result Digest) (binding : ∀ parts state, (call parts state).1 = hashv parts)
    (input : BEj_ReifiedBatch.Input) (slot : Fin 2) (state : S) (before : Log) :
    (native call hashv input slot state before).2.2 =
      before ++ BEi_RecorderCut.issued before (native call hashv input slot state before).2.2 ∧
    BEi_RecorderCut.issued before (native call hashv input slot state before).2.2 =
      (SdkC_Source.run hashv (BEj_ReifiedBatch.sourceCode hashv input slot) []).2 := by
  have localLaw := observation call hashv input slot state before trivial
  have packet := BEj_LocalExport.cut call hashv binding _ state before _ localLaw
  exact ⟨packet.1,packet.2.1⟩

#print axioms observation
#print axioms export_cut
end AspisR1.BEl_ReferenceObservation
end
