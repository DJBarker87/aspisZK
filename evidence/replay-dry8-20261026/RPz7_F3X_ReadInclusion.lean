import RPz7_F3X_SourcePrefix
import RPz7_F3X_Preparation
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3X_ReadInclusion
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence

theorem preparation {F C : Type} (c : Configuration F C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (s : Submission) (H : Bytes → State)
    (e : Evidence c B s H) (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (first : AspisR1CurrentCaller.verifier.candidate.tx1
      (GExp_FirstCode.installed (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry)
        c.boundaries c.std) (D1 c H) (AspisS6CurrentVerifierCarrier.toPublic e.semantic)
        e.pub e.proof 10#usize () none=ok (.Ok e.saved)) :
    ∀ a,FS2.Duplex.Read (eval H (F3X_Preparation.program c s)).1 a →
      FS2.Duplex.Read (eval H (F3T_Installed.source c hashv (input c s))).1 a := by
  obtain ⟨tail,trace⟩ := F3X_SourcePrefix.chronological c B s H e hashv first
  rw [F3X_Preparation.on_evidence c B s H e]
  intro a read
  rw [trace]
  change a∈(_++tail).map Prod.fst
  rw [List.map_append]
  exact List.mem_append_left _ read

#print axioms preparation
end AspisR1.F3X_ReadInclusion
end
