import DrvC_FirstHeadBridge
import DrvC_FirstHead
set_option autoImplicit false
noncomputable section
namespace AspisR1.DrvC_FirstProgram
open Aeneas Aeneas.Std Result
open DrvC_Installation Tx1Q_Carriers DrvC_OraclePort DrvC_OracleNormalize
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
local instance : MonadLift Result SdkC_Source.Code where
  monadLift := CheckpointBytes5Effect.liftResult
theorem program {F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (semantic : Port1_Driver.Semantic) (pub proof : Slice U8) :
    let r := DrvC_FirstConstants.configuration c
    SdkC_Oracle.program (VTop_Flow.tx1 (DrvC_Effects.effects r) (digest r) semantic pub proof 10#usize () none) =
      mapR (DrvC_Dictionary.reply id)
        (GExp_Experiment.first (GExp_FirstPair.base r.currentBase r.reserved r.query r.geometry)
          r.boundaries r.std hashv (currentDigest r)
          ⟨AspisS6CurrentVerifierCarrier.toPublic semantic,pub,proof,10#usize⟩) := by
  dsimp only
  rw [DrvC_FirstHeadBridge.stage]
  have head := DrvC_FirstHead.program c hashv semantic pub proof
  dsimp only at head
  simpa only [GExp_Experiment.first,DrvC_FirstHeadBridge.source] using head

/-- Complete ordered program transport at the literal Port1 TX1 tree. -/
theorem interpreted {F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (semantic : Port1_Driver.Semantic) (pub proof : Slice U8) :
    let r := DrvC_FirstConstants.configuration c
    VTop_OracleCode.interpret (DrvC_Implementation.implementation r)
      (VTop_Flow.tx1 VTop_Flow.traceEffects (digest r) semantic pub proof 10#usize () none) =
      mapR (DrvC_Dictionary.reply id)
        (GExp_Experiment.first (GExp_FirstPair.base r.currentBase r.reserved r.query r.geometry)
          r.boundaries r.std hashv (currentDigest r)
          ⟨AspisS6CurrentVerifierCarrier.toPublic semantic,pub,proof,10#usize⟩) := by
  dsimp only
  rw [← DrvC_CallCode.program_lower,DrvC_Flow.tx1]
  exact program c hashv semantic pub proof

#print axioms program
#print axioms interpreted
end AspisR1.DrvC_FirstProgram
end
