import FIn_FromRead
import SAF_Returns
set_option autoImplicit false
noncomputable section
attribute [local irreducible] QuadraticAlgebra.instInv
namespace AspisR1.FIn_AcceptedRounds
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
open OraclePortCompactDraft OraclePortStoredDecisionDraftC4 RawCutTranscriptRun

/-- Actual successful round operands and their equations. The primitive guards
are reached source calls, not independently assumed successful evaluations. -/
theorem equations {W : Type} (seed : FinishOps W)
    (ops : VTop_Stages.Ops) (proof : Slice U8) (t : Cons_Native.Witness)
    (shape : SAG_NativeFull.Shape ops proof t)
    (s0 : ops.op22=ok 7527#usize) (e0 : ops.op15=ok 7751#usize)
    (s1 : ops.op14=ok 7783#usize) (e1 : ops.op21=ok 8007#usize)
    (parsed : Parsed) (q : Fin 22 → Fin 262144) (tr : ErasedPrefix)
    (d : MatchingSupport.Data AspisWideTower.WideExact)
    (parse : OraclePortStoredParserC4.parseReached (MultiproofConeCanonical.bytesOf proof.val) tr=some parsed)
    (read : LiteralMatchingData.read (typedRows parsed q tr)=some d)
    (s2 : t.p2.variant=.S2)
    (success : Port4D_FinishInstall.finish (FIn_Install.finishOps seed) t.v2 t.p2
      {t.returned2 with weights:=t.back2 t.flushed2} none=ok (.Ok ())) :
    ∃ (alpha0 alpha1 : E) (value0 value1 : E),
      Array.index_usize t.p2.alpha 0#usize=ok alpha0 ∧
      Array.index_usize t.p2.alpha 1#usize=ok alpha1 ∧
      (FIn_Install.finishOps seed).polynomial t.v2.round0 alpha0=ok value0 ∧
      (FIn_Install.finishOps seed).polynomial t.v2.round1 alpha1=ok value1 ∧
      TwoRoundComparison.boundary d.p0=RoundPairing.quarter*CheckpointBytes5Output.ofE t.p2.claim ∧
      TwoRoundComparison.boundary d.p1=RoundPairing.quarter*CheckpointBytes5Output.ofE value0 ∧
      CheckpointBytes5Output.ofE value0=d.p0.eval (CheckpointBytes5Output.ofE alpha0) ∧
      CheckpointBytes5Output.ofE value1=d.p1.eval (CheckpointBytes5Output.ofE alpha1) := by
  have laws := FIn_FromRead.rounds seed ops proof t shape s0 e0 s1 e1 parsed q tr d parse read
  obtain ⟨alpha0,alpha1,r0,r1,weights,alphas,pair,dot,ha0,ha1,hw,has,hp,hd,eq0,eq1,ep,ed⟩ :=
    SAF_Returns.finish (FIn_Install.finishOps seed) t.v2 t.p2 _ s2 success
  have b0 := laws.1.boundary r0.c0 r0.c4 r0.lhs r0.field0 r0.field4 r0.add
  have b1 := laws.2.boundary r1.c0 r1.c4 r1.lhs r1.field0 r1.field4 r1.add
  have q0 := laws.1.quarter r0.quarter t.p2.claim r0.rhs r0.quarter_run r0.multiply
  have q1 := laws.2.quarter r1.quarter r0.value r1.rhs r1.quarter_run r1.multiply
  rw [eq0] at b0
  rw [eq1] at b1
  exact ⟨alpha0,alpha1,r0.value,r1.value,ha0,ha1,r0.evaluate,r1.evaluate,
    b0.symm.trans q0,b1.symm.trans q1,
    laws.1.eval alpha0 r0.value r0.evaluate,laws.2.eval alpha1 r1.value r1.evaluate⟩

#print axioms equations
end AspisR1.FIn_AcceptedRounds
end
