import FIn_PhysicalRounds
import FIn_Payloads
import FIn_Round
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIn_FromRead
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OraclePortCompactDraft OraclePortStoredDecisionDraftC4 RawCutTranscriptRun

theorem rounds {W : Type} (seed : AspisR1Stage2.Stage2Finish.FinishOps W)
    (ops : VTop_Stages.Ops) (proof : Slice U8) (t : Cons_Native.Witness)
    (shape : SAG_NativeFull.Shape ops proof t)
    (s0 : ops.op22=ok 7527#usize) (e0 : ops.op15=ok 7751#usize)
    (s1 : ops.op14=ok 7783#usize) (e1 : ops.op21=ok 8007#usize)
    (parsed : Parsed) (q : Fin 22 → Fin 262144) (tr : ErasedPrefix)
    (d : MatchingSupport.Data AspisWideTower.WideExact)
    (parse : OraclePortStoredParserC4.parseReached (MultiproofConeCanonical.bytesOf proof.val) tr=some parsed)
    (read : LiteralMatchingData.read (typedRows parsed q tr)=some d) :
    Port4D_Pairing.RoundLaws (Port3_FinishStage.release (FIn_Install.finishOps seed))
      CheckpointBytes5Output.ofE t.v2.round0 d.p0 ∧
    Port4D_Pairing.RoundLaws (Port3_FinishStage.release (FIn_Install.finishOps seed))
      CheckpointBytes5Output.ofE t.v2.round1 d.p1 := by
  have observed := OraclePortStoredParserC4.parsed _ _ _ parse
  have physical := FIn_PhysicalRounds.rounds ops proof t shape s0 e0 s1 e1
  rw [←observed.2.1] at physical
  obtain ⟨f0,f1,h0,h1,p0,p1⟩ := FIn_Payloads.from_read parsed q tr d observed.2.2 read
  rw [p0,p1]
  have a := FIn_Round.laws seed t.v2.round0 f0 (h0.trans physical.1.symm)
  have b := FIn_Round.laws seed t.v2.round1 f1 (h1.trans physical.2.symm)
  exact ⟨⟨a.boundary,a.quarter,a.eval⟩,⟨b.boundary,b.quarter,b.eval⟩⟩

#print axioms rounds
end AspisR1.FIn_FromRead
end
