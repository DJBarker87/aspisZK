import Hiq_AccountLoss
import Hiq_CleanWorld
import Hiq_BindingFailure
import Hiq_AccountEvent
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_AccountClean
open Aeneas Aeneas.Std Result GExq_AccountExperiment S2Trust S2W_D189Entry S2W_D189Wrappers
open FS FS2 FS2.Duplex DrvC_Installation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.CausalFirstHitUnionBound
variable {A F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (adversary : Program Bytes State (FirstInputs A))
    (chooseSecond : FirstInputs A → alloc.vec.Vec U8 → Heap (Nat → Record) → A → Program Bytes State (SecondInputs A))

theorem exists_clean
    (prefixBound : ∀ H, (eval H adversary).1.length ≤ 0)
    (choiceBound : ∀ input saved post final H, (eval H (chooseSecond input saved post final)).1.length ≤ 0)
    (project : GExq_AccountExperiment.Outcome A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144)) :
    ∃ H : Bytes → State,
      ¬ BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv 2965
        (eval H (Hiq_DrvRecorded.program c hashv copy allocator id adversary chooseSecond project)) ∧
      R9PoolRuntimeBinding.P2Prime H
        (Hiq_ByteSelection.select (sdk c) id (eval H (Hiq_DrvExperiment.source c hashv copy allocator id adversary chooseSecond)).2).1
        (Hiq_ByteSelection.select (sdk c) id (eval H (Hiq_DrvExperiment.source c hashv copy allocator id adversary chooseSecond)).2).2 := by
  have bound := Hiq_AccountLoss.one_loss c hashv copy allocator id adversary chooseSecond 0 0 prefixBound choiceBound project
  have small : Hiq_Numeric.accountLoss 0 < 1 := by norm_num [Hiq_Numeric.accountLoss]
  obtain ⟨H,clean⟩ := Hiq_CleanWorld.exists_clean _ _ (lt_of_le_of_lt bound small)
  refine ⟨H,clean,?_⟩
  rcases Hiq_JointBinding.binding_or_collision SelectedTranscriptParams.params.iv
      (Hiq_DrvExperiment.source c hashv copy allocator id adversary chooseSecond) project (Hiq_ByteSelection.select (sdk c) id)
      1921 (by simpa only [Nat.zero_add] using
        Hiq_DrvExperiment.source_budget c hashv copy allocator id adversary chooseSecond 0 0 prefixBound choiceBound) H with bad | good
  · apply False.elim
    apply clean
    simpa only [Hiq_DrvRecorded.program,Hiq_RecordedJoint.evaluation,Hiq_DrvExperiment.joint,
      BinRawByteCollisionTargets.event] using bad
  · exact good

#print axioms exists_clean
end AspisR1.Hiq_AccountClean
end
