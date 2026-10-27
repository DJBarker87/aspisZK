import RPz7_FIn_FromRead
import RPz7_FIn_WeightLength
import RPz7_SAG_ShapeDot
import RPz8_F3Y_FinishLeaves
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIn_Derived
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
open OraclePortCompactDraft OraclePortStoredDecisionDraftC4 RawCutTranscriptRun
open scoped BigOperators

def Holds {W : Type} (finish : FinishOps W) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator) (x : F3S_FinishWitness.Primitives finish v p a)
    (parsed : Parsed) (q : Fin 22 → Fin 262144) (tr : ErasedPrefix)
    (data : MatchingSupport.Data AspisWideTower.WideExact) : Prop :=
  Port4D_Pairing.RoundLaws (Port3_FinishStage.release finish) CheckpointBytes5Output.ofE v.round0 data.p0 ∧
  Port4D_Pairing.RoundLaws (Port3_FinishStage.release finish) CheckpointBytes5Output.ofE v.round1 data.p1 ∧
  CheckpointBytes5Output.ofE x.dot=∑ l : Fin 64,data.f l *
    LiteralOpeningView.eK ((CheckpointBytes5Output.accumulator a).weights l)

theorem derive {W C Hash : Type} (finish seed : FinishOps W)
    (installed : finish=FIn_Install.finishOps seed)
    (base : VTop_Stages.Ops) (reserved : Bool) (query : Port3_NativeQueryBody.Ops)
    (geo : Port3_NativeGeometryBody.Ops C) (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub proof checkpoint : Slice U8) (t : Cons_Native.Witness)
    (calls : Cons_Native.Calls base finish reserved query geo D hash pub proof checkpoint t)
    (aux : Cons_NativeBuild.Aux reserved query geo D hash pub proof checkpoint t)
    (saved : t.saved2.weights.val.length=64)
    (ops : VTop_Stages.Ops) (shape : SAG_NativeFull.Shape ops proof t)
    (s0 : ops.op22=ok 7527#usize) (e0 : ops.op15=ok 7751#usize)
    (s1 : ops.op14=ok 7783#usize) (e1 : ops.op21=ok 8007#usize) (last : ops.op20=ok 10055#usize)
    (parsed : Parsed) (q : Fin 22 → Fin 262144) (tr : ErasedPrefix)
    (data : MatchingSupport.Data AspisWideTower.WideExact)
    (parse : OraclePortStoredParserC4.parseReached (MultiproofConeCanonical.bytesOf proof.val) tr=some parsed)
    (read : LiteralMatchingData.read (typedRows parsed q tr)=some data)
    (x : F3S_FinishWitness.Primitives finish t.v2 t.p2 {t.returned2 with weights:=t.back2 t.flushed2}) :
    Holds finish t.v2 t.p2 {t.returned2 with weights:=t.back2 t.flushed2} x parsed q tr data := by
  subst finish
  have rounds := FIn_FromRead.rounds seed ops proof t shape s0 e0 s1 e1 parsed q tr data parse read
  have size := (FIn_WeightLength.twelve reserved query geo D hash pub proof checkpoint t aux saved).1
  have dot := SAG_ShapeDot.value base (FIn_Install.finishOps seed) reserved query geo D hash
    pub proof checkpoint t calls ops shape e1 last rfl size parsed q tr data parse read
  have ⟨_,_,_,_,_,_,_,_,_,finishCall,_⟩ := calls
  have actual := (Port4D_FinishInstall.accepted_dot (FIn_Install.finishOps seed) t.v2 t.p2
    {t.returned2 with weights:=t.back2 t.flushed2} none finishCall).1
  have same := core.result.Result.Ok.inj (Result.ok.inj (x.hd.symm.trans actual))
  exact ⟨rounds.1,rounds.2,by rw [same]; exact dot⟩

#print axioms derive
end AspisR1.FIn_Derived
end
