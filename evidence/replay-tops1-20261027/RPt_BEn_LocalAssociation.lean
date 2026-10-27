import RPt_BEn_ExtractedSlots
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEn_LocalAssociation
open Aeneas Aeneas.Std Result SdkC_Source

/-- Uniform association on the extracted batch's exact operands, all outcomes,
both ordinals and arbitrary state/history. Admission is True because the
source term handles malformed inputs too; no successful Result is assumed. -/
theorem observation {S : Type} (call : Parts → S → Result Digest × S) (hashv : Parts → Result Digest) :
    BEh_Scope.BothSlots (fun (_ : BEn_ExtractedSlots.Input) (_ : Fin 2) (_ : S) => True)
      (BEn_ExtractedSlots.native call hashv) (BEl_NativeBatchCut.source call hashv) := by
  intro input slot state before _
  unfold BEn_ExtractedSlots.native BEn_ExtractedSlots.observe BEl_NativeBatchCut.source
  rw [BEl_PartialRecorder.correspondence, BEn_ExtractedSlots.source]
  exact BEh_Scope.reflexive _

theorem logs {S : Type} (call : Parts → S → Result Digest × S) (hashv : Parts → Result Digest)
    (input : BEn_ExtractedSlots.Input) (slot : Fin 2) (state : S) (before : Log) :
    (BEn_ExtractedSlots.native call hashv input slot state before).2.2 =
      (BEl_NativeBatchCut.source call hashv input slot state before).2.2 :=
  BEh_Scope.logs _ _ (observation call hashv input slot state before trivial)

theorem current {S : Type} (call : Parts → S → Result Digest × S)
    (hashv : Parts → Result Digest) (proof : Slice U8)
    (p : AspisR1CurrentCaller.verifier.Prepared) (root : Digest) (state : S) (before : Log) :
    BEh_Scope.Law (BEn_ExtractedSlots.observe call (BEn_ExtractedSlots.currentBody hashv proof p root) state before)
      (BEf_Carrier.run call (SdkC_BatchSource.currentCode hashv proof p root) state before) := by
  unfold BEn_ExtractedSlots.observe
  rw [BEl_PartialRecorder.correspondence,BEn_ExtractedSlots.current]
  exact BEh_Scope.reflexive _

theorem stage {S : Type} (call : Parts → S → Result Digest × S)
    (hashv : Parts → Result Digest) (proof : Slice U8)
    (p : VTop_Stages.verifier.Prepared) (root : Digest) (state : S) (before : Log) :
    BEh_Scope.Law (BEn_ExtractedSlots.observe call (BEn_ExtractedSlots.stageBody hashv proof p root) state before)
      (BEf_Carrier.run call (SdkC_BatchSource.stageCode hashv proof p root) state before) := by
  unfold BEn_ExtractedSlots.observe
  rw [BEl_PartialRecorder.correspondence,BEn_ExtractedSlots.stage]
  exact BEh_Scope.reflexive _

#print axioms observation
#print axioms logs
#print axioms current
#print axioms stage
end AspisR1.BEn_LocalAssociation
end
