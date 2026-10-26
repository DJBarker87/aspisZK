import SAG_PhysicalShape
import SAG_DotFromRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAG_ShapeDot
open Aeneas Aeneas.Std Result
open AspisR1Stage2
open OraclePortCompactDraft OraclePortStoredDecisionDraftC4 RawCutTranscriptRun
open scoped BigOperators

theorem value {F C Hash : Type} (base : VTop_Stages.Ops)
    (finish : Stage2Finish.FinishOps F) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub proof checkpoint : Slice U8) (t : Cons_Native.Witness)
    (calls : Cons_Native.Calls base finish reserved query geo D hash pub proof checkpoint t)
    (shapeOps : VTop_Stages.Ops) (shape : SAG_NativeFull.Shape shapeOps proof t)
    (start : shapeOps.op21 = ok 8007#usize) (stop : shapeOps.op20 = ok 10055#usize)
    (installed : finish.dot = SAG_DotClosed.source)
    (length : (t.back2 t.flushed2).val.length = 64)
    (parsed : Parsed) (q : Fin 22 → Fin 262144) (tr : ErasedPrefix)
    (data : MatchingSupport.Data AspisWideTower.WideExact)
    (parse : OraclePortStoredParserC4.parseReached (MultiproofConeCanonical.bytesOf proof.val) tr = some parsed)
    (read : LiteralMatchingData.read (typedRows parsed q tr) = some data) :
    let a := {t.returned2 with weights := t.back2 t.flushed2}
    CheckpointBytes5Output.ofE a.rhs = ∑ l : Fin 64, data.f l *
      LiteralOpeningView.eK ((CheckpointBytes5Output.accumulator a).weights l) := by
  have observed := OraclePortStoredParserC4.parsed _ _ _ parse
  have physical := SAG_PhysicalShape.final shapeOps proof t shape start stop
  rw [←observed.2.1] at physical
  have ⟨_,_,_,_,_,_,_,_,_,success,_⟩ := calls
  have dotRun := (Port4D_FinishInstall.accepted_dot finish t.v2 t.p2
    {t.returned2 with weights := t.back2 t.flushed2} none success).1
  exact SAG_DotFromRead.value finish t.v2 {t.returned2 with weights := t.back2 t.flushed2}
    t.returned2.rhs parsed q tr data installed length observed.2.2 read physical dotRun

#print axioms value
end AspisR1.SAG_ShapeDot
end
