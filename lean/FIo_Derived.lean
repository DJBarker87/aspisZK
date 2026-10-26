import FIo_Nonvacuity
import FIn_FromRead
import FIn_WeightLength
import SAG_ShapeDot
import F3Y_FinishLeaves
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIo_Derived
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

theorem derive {C Hash : Type} (r : NP6_StdModel.Reservation) (seed : FinishOps FIo_Install.W)
    (base : VTop_Stages.Ops) (reserved : Bool) (query : Port3_NativeQueryBody.Ops)
    (geo : Port3_NativeGeometryBody.Ops C) (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub proof checkpoint : Slice U8) (t : Cons_Native.Witness)
    (calls : Cons_Native.Calls base (FIo_Install.finishOps r seed) reserved query geo D hash pub proof checkpoint t)
    (aux : Cons_NativeBuild.Aux reserved query geo D hash pub proof checkpoint t)
    (saved : t.saved2.weights.val.length=64)
    (ops : VTop_Stages.Ops) (shape : SAG_NativeFull.Shape ops proof t)
    (s0 : ops.op22=ok 7527#usize) (e0 : ops.op15=ok 7751#usize)
    (s1 : ops.op14=ok 7783#usize) (e1 : ops.op21=ok 8007#usize) (last : ops.op20=ok 10055#usize)
    (parsed : Parsed) (q : Fin 22 → Fin 262144) (tr : ErasedPrefix)
    (data : MatchingSupport.Data AspisWideTower.WideExact)
    (parse : OraclePortStoredParserC4.parseReached (MultiproofConeCanonical.bytesOf proof.val) tr=some parsed)
    (read : LiteralMatchingData.read (typedRows parsed q tr)=some data)
    (x : F3S_FinishWitness.Primitives (FIo_Install.finishOps r seed) t.v2 t.p2 {t.returned2 with weights:=t.back2 t.flushed2}) :
    Holds (FIo_Install.finishOps r seed) t.v2 t.p2 {t.returned2 with weights:=t.back2 t.flushed2} x parsed q tr data  := by
  exact FIn_Derived.derive (FIo_Install.finishOps r seed) (FIo_Install.finishOps r seed)
    (FIo_Nonvacuity.arithmetic_fixed r seed).symm base reserved query geo D hash pub proof checkpoint t
    calls aux saved ops shape s0 e0 s1 e1 last parsed q tr data parse read x

#print axioms derive
end AspisR1.FIo_Derived
end
