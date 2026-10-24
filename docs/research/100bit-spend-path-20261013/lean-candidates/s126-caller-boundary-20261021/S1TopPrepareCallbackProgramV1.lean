import S1TopPrepareBudgetV1
import S1PreparedPowersScratchV1
set_option autoImplicit false
noncomputable section
namespace AspisS1TopPrepareCode
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.PreparedHashCode
open AspisS1TopPrepareCarrier AspisS1PreparedPowersCallbacks
open AspisS1PowersCallbackChain AspisR1PowersConcreteMul AspisR1PowersExactProduct
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw
open S4SolanaDigestWrapperP3BindingV1

/-- Same accepted response-driven op7 execution, full source effects/result,
read count, and exact raw scratch/callback correspondence. Seed ranges,
callback totality, final multiplication and scratch matching are derived.
Actual frozen native/SDK/Std installation remains a separate source boundary. -/
theorem accepted_callback_scratch (base : AspisR1CurrentCaller.Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (other : AspisR1.VTop_OracleCode.Implementation) (H : Bytes → State)
    (pub : VTop_Stages.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : SolanaDigest) (input scratch : Array Top.E 29#usize) (prepared : Top.Prepared)
    (accepted : (eval H (body base R B other
      (.op7 (digest (fun bytes => encodeState (H bytes))) pub proof hash none input))).2=
        ok (.Ok prepared,scratch)) :
    eval H (body base R B other
      (.op7 (digest (fun bytes => encodeState (H bytes))) pub proof hash none input))=
      (observe (run (code base R B (digest (fun bytes => encodeState (H bytes))) pub proof hash input)).1,
        AspisS1TopPrepareSource.prepare (sourceOps base R B) (digest (fun bytes => encodeState (H bytes)))
          pub proof hash none input) ∧
    (eval H (body base R B other
      (.op7 (digest (fun bytes => encodeState (H bytes))) pub proof hash none input))).1.length ≤ 115 ∧
    ∃ last,
      execute 29#usize (one,callbackE prepared.gamma) (slots 29#usize)=
        ok (scratch.val.map callbackE,(last,callbackE prepared.gamma)) ∧
      Canonical last ∧ decode last=decode (callbackE prepared.gamma)^29 ∧
      Complete 7#usize (callbackE prepared.kappa) := by
  have effects := installed_effects_count base R B other H pub proof hash input
  have source : AspisS1TopPrepareSource.prepare (sourceOps base R B)
      (digest (fun bytes => encodeState (H bytes))) pub proof hash none input=ok (.Ok prepared,scratch) := by
    rw [effects.1] at accepted
    exact accepted
  exact ⟨effects.1,effects.2,prepared_scratch_callbacks (sourceOps base R B) _ pub proof hash input scratch prepared source⟩

#print axioms accepted_callback_scratch
end AspisS1TopPrepareCode
