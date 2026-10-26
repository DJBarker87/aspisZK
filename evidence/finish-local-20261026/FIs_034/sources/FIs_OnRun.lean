import FIs_Finish
import FIs_Native
import FIn_FromRead
import FIn_WeightLength
import SAG_ShapeDot
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIs_OnRun
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
open MultiproofConeCanonical OraclePortCompactDraft OraclePortStoredDecisionDraftC4
open RecordedBinaryExperimentBin (SourceInputs)

theorem strengthen {F C Hash : Type} (base : VTop_Stages.Ops) (finish seed : FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub proof checkpoint : Slice U8) (saved : alloc.vec.Vec U8) (t : Cons_Native.Witness)
    (calls : Cons_Native.Calls base finish reserved query geo D hash pub proof checkpoint t)
    (aux : Cons_NativeBuild.Aux reserved query geo D hash pub proof checkpoint t)
    (shapeOps : VTop_Stages.Ops) (shape : SAG_NativeFull.Shape shapeOps proof t)
    (s0 : shapeOps.op22=ok 7527#usize) (e0 : shapeOps.op15=ok 7751#usize)
    (s1 : shapeOps.op14=ok 7783#usize) (e1 : shapeOps.op21=ok 8007#usize) (last : shapeOps.op20=ok 10055#usize)
    (installed : finish=FIn_Install.finishOps seed) (size : t.saved2.weights.val.length=64)
    (H : Bytes → State) (stored publicBytes : Bytes)
    (tx1p : AspisR1CurrentCaller.verifier.Prepared) (authParsed parsed : Parsed)
    (trace : List (Bytes × State)) (q : Fin 22 → Fin 262144)
    (tr : RawCutTranscriptRun.ErasedPrefix) (i : SourceInputs) (c : OraclePortCheckpointResumeC5.Context)
    (parser : OraclePortStoredParserC4.parseReached (bytesOf proof.val) tr=some parsed)
    (read : LiteralMatchingData.read (typedRows parsed q tr)=some i.data)
    (old : SAF_C_SAF_FinishPrepared.Outcome finish t.v2 t.p2
      {t.returned2 with weights:=t.back2 t.flushed2} proof saved H stored publicBytes tx1p authParsed trace
      parsed.semantic q tr i c) :
    FIs_Finish.Outcome finish t.v2 t.p2 {t.returned2 with weights:=t.back2 t.flushed2}
      proof saved H stored publicBytes tx1p authParsed trace parsed.semantic q tr i c := by
  have rounds := FIn_FromRead.rounds seed shapeOps proof t shape s0 e0 s1 e1 parsed q tr i.data parser read
  have length := (FIn_WeightLength.twelve reserved query geo D hash pub proof checkpoint t aux size).1
  have dot := SAG_ShapeDot.value base finish reserved query geo D hash pub proof checkpoint t calls
    shapeOps shape e1 last (by rw [installed]; rfl) length parsed q tr i.data parser read
  apply FIs_Finish.strengthen (old := old)
  · rw [installed]; exact rounds.1
  · rw [installed]; exact rounds.2
  · exact dot

#print axioms strengthen
end AspisR1.FIs_OnRun
end
