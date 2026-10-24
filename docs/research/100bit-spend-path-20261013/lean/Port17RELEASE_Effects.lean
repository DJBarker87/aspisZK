import Port17RELEASE_Prepare
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port17RELEASE_Effects
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.PreparedHashCode AspisR1PublicPreparation.PreparedBudget
open AspisS1TopPrepareCarrier AspisS1TopPrepareCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw
open S4SolanaDigestWrapperP3BindingV1
theorem op7_effects_count (ops : VTop_Stages.Ops) (reserved : Bool) (unwrap : AspisR1.Port6CK_Semantic.Unwrap)
    (base : AspisR1CurrentCaller.Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (other : AspisR1.VTop_OracleCode.Implementation) (H : Bytes → State)
    (pub : VTop_Stages.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : SolanaDigest) (input : Array Top.E 29#usize) :
    eval H (AspisR1.Port17RELEASE_Prepare.implementation ops reserved unwrap base R B other
      (.op7 (digest (fun bytes => encodeState (H bytes))) pub proof hash none input))=
      (observe (run (code base R B (digest (fun bytes => encodeState (H bytes))) pub proof hash input)).1,
        AspisS1TopPrepareSource.prepare (sourceOps base R B) (digest (fun bytes => encodeState (H bytes)))
          pub proof hash none input) ∧
    (eval H (AspisR1.Port17RELEASE_Prepare.implementation ops reserved unwrap base R B other
      (.op7 (digest (fun bytes => encodeState (H bytes))) pub proof hash none input))).1.length ≤ 115 := by
  exact AspisS1TopPrepareCode.installed_effects_count base R B other H pub proof hash input

#print axioms op7_effects_count
end AspisR1.Port17RELEASE_Effects
end
