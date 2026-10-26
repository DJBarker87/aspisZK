import RPz7_DrvC_FirstHeadSyntax
import RPz7_DrvC_FirstTail
set_option autoImplicit false
noncomputable section
namespace AspisR1.DrvC_FirstHead
open Aeneas Aeneas.Std Result
open DrvC_Installation Tx1Q_Carriers DrvC_OraclePort DrvC_OracleNormalize
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
local instance : MonadLift Result SdkC_Source.Code where
  monadLift := CheckpointBytes5Effect.liftResult
attribute [local irreducible] DrvC_FirstSyntax.stageTail DrvC_FirstSyntax.sourceTail
  SdkD_PrepareLower.lower

theorem prepare_repeat {F C : Type} (c : Configuration F C)
    (semantic : Port1_Driver.Semantic) (proof : Slice U8) (zero : Tx1Q_Carriers.C.E) :
    SdkC_Oracle.program (DrvC_CallCode.code c
      (.op7 (digest c) semantic proof () none (Array.repeat 29#usize (e zero)))) =
      mapR DrvC_Dictionary.prepareReply
        (SdkC_Oracle.program (SdkD_PrepareLower.lower (SdkD_PrepareSource.code
          (Op5T_Concrete.current
            {GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry with op16 := Tx1Q_Install.writer})
          c.boundaries c.std (currentDigest c)
          (AspisS6CurrentVerifierCarrier.toPublic semantic) proof () (Array.repeat 29#usize zero)))) := by
  rw [← DrvC_CurrentSlots.arr_repeat]
  exact DrvC_FirstPrograms.prepare c semantic proof _

theorem program {F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (semantic : Port1_Driver.Semantic) (pub proof : Slice U8) :
    let r := DrvC_FirstConstants.configuration c
    SdkC_Oracle.program (DrvC_FirstHeadSyntax.stageHead r semantic pub proof 10#usize) =
      mapR (DrvC_Dictionary.reply id)
        (SdkC_Oracle.program (DrvC_FirstHeadSyntax.sourceHead r hashv semantic pub proof 10#usize)) := by
  dsimp only
  simp only [DrvC_FirstHeadSyntax.stageHead,DrvC_FirstHeadSyntax.sourceHead,DrvC_Effects.effects,
    program_bindM,program_lift,program_pure,program_if,map_bind,
    DrvC_FirstLibrary.split,DrvC_FirstTail.bindR_ok,
    AspisR1CurrentCaller.compact.SPLIT,bne_self_eq_false,Bool.false_eq_true,if_false]
  all_goals repeat' first
    | (with_reducible rfl)
    | (fail_if_no_progress simp only [program_bindM,program_lift,program_pure,program_if,
        map_bind,bind_map,map_pure,DrvC_FirstTail.bindR_ok,
        DrvC_FirstPrograms.shape,DrvC_FirstPrograms.scan,DrvC_FirstPrograms.zero,
        DrvC_FirstLibrary.mark,prepare_repeat,DrvC_FirstTail.program c hashv,
        DrvC_Dictionary.reply,DrvC_Dictionary.prepareReply,AspisR1CurrentCaller.verifier.mark,
        core.result.Result.Insts.CoreOpsTry.branch])
    | (apply bindR_congr; intro x)
    | casesm (core.result.Result _ _)
    | casesm (_ × _)
    | split
  all_goals rfl

#print axioms prepare_repeat
#print axioms program
end AspisR1.DrvC_FirstHead
end
