import RPv_FJs_LiteralPair
import RPv_FJs_Finish
import RPz7_SAG_PhysicalShape
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJs_OnRun
open Aeneas Aeneas.Std Result AspisR1Stage2
open MultiproofConeCanonical OraclePortCompactDraft OraclePortStoredDecisionDraftC4 RawCutTranscriptRun
attribute [local irreducible] QuadraticAlgebra.instInv

theorem law (r : NP6_StdModel.Reservation) (seed : Stage2Finish.FinishOps FIo_Install.W)
    (proof : Slice U8) (t : Cons_Native.Witness) (ops : VTop_Stages.Ops)
    (shape : SAG_NativeFull.Shape ops proof t)
    (start : ops.op21=ok 8007#usize) (stop : ops.op20=ok 10055#usize)
    (parsed : Parsed) (q : Fin 22 → Fin 262144) (tr : ErasedPrefix)
    (data : RecordedBinaryExperimentBin.SourceInputs) (view : LiteralOpeningView.View)
    (parser : OraclePortStoredParserC4.parseReached (bytesOf proof.val) tr=some parsed)
    (read : LiteralMatchingData.read (typedRows parsed q tr)=some data.data)
    (opening : LiteralOpeningView.read (typedRows parsed q tr)=some view)
    (am : QueryAccumulator.State OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E)
    (fields : CheckpointBytes4SavedFields.BodyMatches t.p2 t.saved2
      (OraclePortCheckpointResumeC5.prepared (OraclePortAcceptedContextC6.context parsed data view)
        data.data (SelectedChallengeMap.rhoOf data.rho) q) am)
    (range : ∀ j : Fin 10,FIr_SampleRange.InBase ((view.semantic.map Prod.snd).getD (15+j.val) 0)) :
    FIn_Finish.PairMeaning (FIo_Install.finishOps r seed) t.v2 t.p2 data.data := by
  have observed := OraclePortStoredParserC4.parsed _ _ _ parser
  have physical := SAG_PhysicalShape.final ops proof t shape start stop
  rw [←observed.2.1] at physical
  have encoded := (SAG_FinalPayload.from_read parsed q tr data.data observed.2.2 read).trans physical.symm
  exact FJs_LiteralPair.value r seed t.v2 t.p2 t.saved2 parsed data view q am fields
    (typedRows parsed q tr) read opening range encoded

#print axioms law
end AspisR1.FJs_OnRun
end
