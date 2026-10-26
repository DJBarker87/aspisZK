import FIn_Install
import FIn_WeightLength
import SAG_ShapeDot
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIn_Dot
open Aeneas Aeneas.Std Result AspisR1Stage2
open OraclePortCompactDraft OraclePortStoredDecisionDraftC4 RawCutTranscriptRun
open scoped BigOperators

theorem value {W C Hash : Type} (seed : Stage2Finish.FinishOps W)
    (base : VTop_Stages.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub proof checkpoint : Slice U8) (t : Cons_Native.Witness)
    (calls : Cons_Native.Calls base (FIn_Install.finishOps seed) reserved query geo D hash pub proof checkpoint t)
    (aux : Cons_NativeBuild.Aux reserved query geo D hash pub proof checkpoint t)
    (prepared : OraclePortCheckpointAbiC5.Prepared)
    (am : QueryAccumulator.State OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E)
    (fields : CheckpointBytes4SavedFields.BodyMatches t.p2 t.saved2 prepared am)
    (shapeOps : VTop_Stages.Ops) (shape : SAG_NativeFull.Shape shapeOps proof t)
    (start : shapeOps.op21=ok 8007#usize) (stop : shapeOps.op20=ok 10055#usize)
    (parsed : Parsed) (q : Fin 22 → Fin 262144) (tr : ErasedPrefix)
    (data : MatchingSupport.Data AspisWideTower.WideExact)
    (parse : OraclePortStoredParserC4.parseReached (MultiproofConeCanonical.bytesOf proof.val) tr=some parsed)
    (read : LiteralMatchingData.read (typedRows parsed q tr)=some data) :
    let a := {t.returned2 with weights:=t.back2 t.flushed2}
    CheckpointBytes5Output.ofE a.rhs=∑ l : Fin 64,data.f l *
      LiteralOpeningView.eK ((CheckpointBytes5Output.accumulator a).weights l) := by
  have saved : t.saved2.weights.val.length=64 := by
    rw [fields.weights]
    simp only [List.length_map,List.length_ofFn]
  have size := (FIn_WeightLength.twelve reserved query geo D hash pub proof checkpoint t aux saved).1
  exact SAG_ShapeDot.value base (FIn_Install.finishOps seed) reserved query geo D hash
    pub proof checkpoint t calls shapeOps shape start stop rfl size parsed q tr data parse read

#print axioms value
end AspisR1.FIn_Dot
end
