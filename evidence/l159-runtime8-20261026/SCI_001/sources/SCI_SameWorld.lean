import SCH_AccountDecoded
import SCE_SecondCutBytes
import SCE_FixtureGame
import SCE_FixtureSubmission
import SCE_FixtureRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCI_SameWorld
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment S2W_NativeConsolidation
open MultiproofConeCanonical

/-- Exact per-world association actually available from the interpreter. The
checkpoint is the selected second ENTRY's buffer; equality to saved is not
asserted. The public/proof submission is the first submission, as in SCE_. -/
theorem assoc {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (err : C) (reservation : NP6_StdModel.Reservation)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A)
    (H : Bytes → State) :
    let r := Rc5_Install.configuration err c reservation
    accepted (eval H (account r hashv copy allocator id a)).2 = true →
    ∃ saved post final f s,
      SourceCuts (SCH_IdealSdk.dictionary r hashv H) (eval H a.first).2.entry.first
        ((eval H (a.second (eval H a.first).2 saved post final)).2.entry.second secondSizes)
        saved f s ∧
      Port1_Driver.decodeSemantic (DrvC_Installation.sdk r) f.pub = ok (some f.semantic) ∧
      (eval H (submission a)).2 =
        (⟨bytesOf f.pub.val,bytesOf f.proof.val⟩ : F3T_ByteCarrier.Submission) ∧
      bytesOf s.checkpoint.val = bytesOf
        ((eval H (a.second (eval H a.first).2 saved post final)).2.entry.buffers
          ((eval H (a.second (eval H a.first).2 saved post final)).2.entry.handles 6).1).val := by
  dsimp only
  intro success
  obtain ⟨saved,post,final,f,s,cuts,decoded,submitted⟩ :=
    SCH_AccountDecoded.accepted c err reservation hashv copy allocator id a H success
  exact ⟨saved,post,final,f,s,cuts,decoded,submitted,
    SCE_SecondCutBytes.checkpoint _ _ _ saved f s cuts⟩

/-- An admitted adversary may ignore the saved checkpoint and choose ANY
second entry. This is a language fact, not a cryptographic acceptance claim. -/
theorem arbitrary_second {A : Type} (i : GExq_AccountExperiment.FirstInputs A)
    (j : GExq_AccountExperiment.SecondInputs A) :
    ∃ a : Adversary A, ∀ (H : Bytes → State) saved post final,
      (eval H a.first).2 = i ∧ (eval H (a.second i saved post final)).2 = j := by
  exact ⟨⟨.done i,fun _ _ _ _ => .done j⟩,fun _ _ _ _ => ⟨rfl,rfl⟩⟩

/-- A checked obstruction to deriving second-input association from the
approved game's fields alone. Its supplied bank pair and persistence remain
inhabited while a distinct SCE second entry can have an empty CP. This does
NOT refute the acceptance-guarded theorem with a game indexed by that entry. -/
def emptyCheckpoint : Entry :=
  { SCE_FixtureData.e2 with buffers := fun _ => SCE_FixtureData.zeros 0 (by decide) }

theorem game_does_not_select_second (data1 data2 : Slice U8)
    (slot : S2W_ExtractionBoundary.Slot) :
    CPH_Game.DeployedPairExecution SCE_FixtureData.observations false true
      SCE_FixtureData.e1 SCE_FixtureData.e2 SCE_FixtureData.saved SCE_FixtureData.suffix
      SCE_FixtureData.n1 SCE_FixtureData.n2 SCE_FixtureData.copy SCE_FixtureData.allocator
      SCE_FixtureData.id ∧
    CPR_DataPersistence.TwoTransactionLaw
      (CPG_Projection.adjacent SCE_FixtureData.observations)
      (CPG_Projection.ordinary SCE_FixtureData.observations (Hist_Nonvacuity.key 0#u8))
      (CPG_Projection.before SCE_FixtureData.observations)
      (CPG_Projection.tentative SCE_FixtureData.observations)
      (CPG_Projection.success SCE_FixtureData.observations)
      (CPG_Projection.loaded SCE_FixtureData.observations) ∧
    ∃ a : Adversary Unit, ∀ (H : Bytes → State) saved post final,
      (eval H a.first).2 = SCE_FixtureSubmission.firstInput data1 ∧
      (eval H (a.second (SCE_FixtureSubmission.firstInput data1) saved post final)).2.entry = emptyCheckpoint ∧
      bytesOf (emptyCheckpoint.buffers (emptyCheckpoint.handles 6).1).val ≠
        bytesOf SCE_FixtureData.saved.val := by
  refine ⟨SCE_FixtureGame.game,SCE_FixtureGame.persistence _,?_,?_⟩
  · exact ⟨.done (SCE_FixtureSubmission.firstInput data1),
      fun _ _ _ _ => .done ⟨emptyCheckpoint,data2,slot,()⟩⟩
  · intro H saved post final
    refine ⟨rfl,rfl,?_⟩
    intro equal
    have length := congrArg List.length equal
    have savedLength : (bytesOf SCE_FixtureData.saved.val).length = 1768 := by
      rw [bytesOf,List.length_map,SCE_FixtureShape.size_saved]
    rw [savedLength] at length
    change 0 = 1768 at length
    omega

#print axioms assoc
#print axioms arbitrary_second
#print axioms game_does_not_select_second
end AspisR1.SCI_SameWorld
end
