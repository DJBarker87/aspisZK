import S1TopPrepareCausalV1
set_option autoImplicit false
noncomputable section
namespace AspisS1TopPrepareCode
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.PreparedHashCode
open AspisS1TopPrepareCarrier
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw
open S4SolanaDigestWrapperP3BindingV1

/-- The complete interface at the lead's Bytes→State oracle type. Array/state
conversion is bijective; there is no restriction to a subset of oracle replies. -/
theorem oracle_exact (base : AspisR1CurrentCaller.Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (H : Bytes → State)
    (pub : VTop_Stages.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : SolanaDigest) (input : Array Top.E 29#usize) :
    eval H (program base R B pub proof hash input)=
      (observe (run (code base R B (digest (fun bytes => encodeState (H bytes))) pub proof hash input)).1,
        AspisS1TopPrepareSource.prepare (sourceOps base R B) (digest (fun bytes => encodeState (H bytes)))
          pub proof hash none input) := by
  simpa only [state_roundtrip] using
    causal_exact base R B (fun bytes => encodeState (H bytes)) pub proof hash input

theorem installed_oracle (base : AspisR1CurrentCaller.Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (other : AspisR1.VTop_OracleCode.Implementation) (H : Bytes → State)
    (pub : VTop_Stages.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : SolanaDigest) (input : Array Top.E 29#usize) :
    eval H (body base R B other
      (.op7 (digest (fun bytes => encodeState (H bytes))) pub proof hash none input))=
      (observe (run (code base R B (digest (fun bytes => encodeState (H bytes))) pub proof hash input)).1,
        AspisS1TopPrepareSource.prepare (sourceOps base R B) (digest (fun bytes => encodeState (H bytes)))
          pub proof hash none input) := by
  simpa only [state_roundtrip] using
    installed_effects base R B other (fun bytes => encodeState (H bytes)) pub proof hash input

#print axioms oracle_exact
#print axioms installed_oracle
end AspisS1TopPrepareCode
