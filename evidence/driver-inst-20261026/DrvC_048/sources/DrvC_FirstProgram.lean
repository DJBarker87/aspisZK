import DrvC_FirstLibrary
set_option autoImplicit false
noncomputable section
namespace AspisR1.DrvC_FirstProgram
open Aeneas Aeneas.Std Result
open DrvC_Installation Tx1Q_Carriers DrvC_OraclePort DrvC_OracleNormalize
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
local instance : MonadLift Result SdkC_Source.Code where
  monadLift := CheckpointBytes5Effect.liftResult
attribute [local irreducible] SdkD_PrepareLower.lower SdkC_BatchSource.currentCode
  GExp_FirstCode.writerCode

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
  simp only [VTop_Flow.tx1,GExp_Experiment.first,GExp_FirstCode.code,
    ← current_dictionary (DrvC_FirstConstants.configuration c),DrvC_Effects.effects,
    program_bindM,program_lift,program_pure,program_if,
    DrvC_FirstLibrary.split,bindR_done,VTop_OracleCode.continueWith,
    AspisR1CurrentCaller.compact.SPLIT,bne_self_eq_false,Bool.false_eq_true,if_false,
    map_bind]
  all_goals repeat' first
    | (solve | rfl)
    | (fail_if_no_progress simp only [program_bindM,program_lift,program_pure,program_if,
        map_bind,bind_map,map_lift,map_pure,bindR_done,VTop_OracleCode.continueWith,
        DrvC_FirstPrograms.shape,DrvC_FirstPrograms.scan,DrvC_FirstPrograms.zero,
        DrvC_FirstPrograms.initial,DrvC_FirstPrograms.prepare,
        DrvC_FirstPrograms.batch (DrvC_FirstConstants.configuration c) hashv,
        DrvC_FirstPrograms.query,DrvC_FirstPrograms.geometry_call,
        DrvC_FirstPrograms.pending_call,DrvC_FirstPrograms.flush,
        DrvC_FirstLibrary.mark,DrvC_FirstLibrary.folded,DrvC_FirstLibrary.round1,
        DrvC_FirstLibrary.unwrap,DrvC_FirstConstants.folded,DrvC_FirstConstants.round1,
        DrvC_FirstPrepare.writer,DrvC_Dictionary.reply,DrvC_Dictionary.prepareReply,
        ← DrvC_CurrentSlots.arr_repeat e 29#usize])
    | (apply bindR_congr; intro x)
    | casesm (core.result.Result _ _)
    | casesm (_ × _)
    | split

#print axioms program
end AspisR1.DrvC_FirstProgram
end
