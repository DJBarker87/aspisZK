import RPz7_DrvC_FirstSyntax
import RPz7_DrvC_Mutable
set_option autoImplicit false
noncomputable section
namespace AspisR1.DrvC_FirstTail
open Aeneas Aeneas.Std Result
open DrvC_Installation Tx1Q_Carriers DrvC_OraclePort DrvC_OracleNormalize
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
local instance : MonadLift Result SdkC_Source.Code where
  monadLift := CheckpointBytes5Effect.liftResult
attribute [local irreducible] SdkC_BatchSource.currentCode GExp_FirstCode.writerCode

theorem bindR_ok {A B : Type} (a : A) (k : A → Port B) : bindR (.done (.ok a)) k = k a := rfl

theorem program {F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (pub proof : Slice U8)
    (p : Tx1Q_Carriers.C.P) (g : Array Tx1Q_Carriers.C.E 29#usize) :
    let r := DrvC_FirstConstants.configuration c
    SdkC_Oracle.program (DrvC_FirstSyntax.stageTail r pub proof 10#usize (prepared p) (arr e g)) =
      mapR (DrvC_Dictionary.reply id)
        (SdkC_Oracle.program (DrvC_FirstSyntax.sourceTail r hashv pub proof 10#usize p g)) := by
  dsimp only
  simp only [DrvC_FirstSyntax.stageTail,DrvC_FirstSyntax.sourceTail,DrvC_Effects.effects,
    program_bindM,program_lift,program_pure,map_bind]
  all_goals repeat' first
    | (with_reducible rfl)
    | (fail_if_no_progress simp only [program_bindM,program_lift,program_pure,program_if,
        map_bind,bind_map,map_pure,bindR_ok,
        DrvC_FirstPrograms.initial,DrvC_FirstPrograms.batch (DrvC_FirstConstants.configuration c) hashv,
        DrvC_FirstPrograms.query,DrvC_FirstPrograms.geometry_call,
        DrvC_FirstPrograms.pending_call,DrvC_FirstPrograms.flush,
        DrvC_FirstLibrary.mark,DrvC_FirstLibrary.folded,DrvC_FirstLibrary.round1,DrvC_FirstLibrary.unwrap,
        DrvC_FirstConstants.folded,DrvC_FirstConstants.round1,DrvC_FirstPrepare.writer,
        DrvC_Dictionary.reply,AspisR1CurrentCaller.verifier.mark,
        core.result.Result.Insts.CoreOpsTry.branch,
        DrvC_Mutable.deref,DrvC_Mutable.deref_mut_current,DrvC_Mutable.deref_mut_stage,
        DrvC_Mutable.materialize,lift])
    | (apply bindR_congr; intro x)
    | casesm (core.result.Result _ _)
    | casesm (_ × _)
    | split
  all_goals rfl

#print axioms bindR_ok
#print axioms program
end AspisR1.DrvC_FirstTail
end
