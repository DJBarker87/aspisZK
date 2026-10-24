import S1CurrentPrepareCodeExactV1
import S1SemanticCodeP3ValidV1
import S1SemanticCodeDictionaryV1
import S1ClosedPreparationCausalProgramV1
set_option autoImplicit false
noncomputable section
namespace AspisR1CurrentCaller.S1PrepareCode
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.PreparedHashCode
open AspisS1ValuesOwnedInstallation BorrowedClaimPrepared
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw
open S4SolanaDigestWrapperP3BindingV1

private theorem semantic_dictionary {H : Type}
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (first second : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) :
    oracleProgram (S1SemanticCodeInstallation.code R B first pub bytes hash)=
      oracleProgram (S1SemanticCodeInstallation.code R B second pub bytes hash) := by
  unfold S1SemanticCodeInstallation.code
  apply oracleProgram_bind_congr
  · apply AspisR1PublicPreparation.S1SemanticCode.verify_dictionary_irrelevant
  · intro result
    rfl

private theorem semantic_valid
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (sha : Bytes → Array U8 32#usize)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : SolanaDigest) :
    OracleValid sha (S1SemanticCodeInstallation.code R B (p3CallerDigest sha) pub bytes hash) := by
  unfold S1SemanticCodeInstallation.code
  apply valid_bind
  · have roundtrip (d : AspisR1PublicPreparation.aspis_core.Digest32 SolanaDigest) :
        InstalledPreparation.retainedDigest (publicToCurrent d)=d := by cases d;rfl
    unfold p3CallerDigest
    rw [roundtrip,p3_public_record_eq_model]
    apply AspisR1PublicPreparation.S1SemanticCode.verify_p3_valid
  · intro result
    exact valid_pure sha _

/-- Complete outer prepare program is independent of the digest dictionary.
Both full hash-bearing source phases are instantiated, without trace premises. -/
theorem dictionary_irrelevant (base : Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    {H : Type} (first second : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H)
    (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    oracleProgram (prepare base R B first pub proof hash scratch)=
      oracleProgram (prepare base R B second pub proof hash scratch) := by
  unfold prepare
  repeat' first
    | (solve | with_reducible apply semantic_dictionary)
    | (solve | with_reducible apply closedPreparation_dictionary_irrelevant)
    | (solve | with_reducible rfl)
    | with_reducible apply oracleProgram_bind_congr
    | intro x
    | split

theorem p3_valid (base : Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (sha : Bytes → Array U8 32#usize)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : SolanaDigest)
    (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    OracleValid sha (prepare base R B (p3CallerDigest sha) pub proof hash scratch) := by
  unfold prepare
  repeat' first
    | (solve | with_reducible apply semantic_valid)
    | (solve | with_reducible apply closedPreparation_p3_valid)
    | (solve | with_reducible apply valid_lift)
    | (solve | with_reducible apply valid_pure)
    | with_reducible apply valid_bind
    | intro x
    | split

/-- Fixed before the sampled oracle. All digest continuations consume actual
ask replies, including the semantic phase BEFORE original Prepared::new. -/
def program (base : Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : SolanaDigest)
    (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize) :=
  oracleProgram (prepare base R B (p3CallerDigest (fun _ => Array.repeat 32#usize 0#u8))
    pub proof hash scratch)

/-- ALL outcomes and ordered query prefixes, no assumed child run,
OracleValid, all-H agreement or desired source-log equality. -/
theorem causal_exact (base : Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (sha : Bytes → Array U8 32#usize)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : SolanaDigest)
    (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    eval (fun bytes => decodeState (sha bytes)) (program base R B pub proof hash scratch)=
      (observe (run (prepare base R B (p3CallerDigest sha) pub proof hash scratch)).1,
        verifier.candidate.prepare (NativeBuffers.install (withValues base) nativeValues R B)
          (p3CallerDigest sha) pub proof hash none scratch) := by
  unfold program
  rw [dictionary_irrelevant base R B _ (p3CallerDigest sha)]
  rw [oracleProgram_exact sha _ (p3_valid base R B sha pub proof hash scratch),run_value]

#print axioms dictionary_irrelevant
#print axioms p3_valid
#print axioms causal_exact
end AspisR1CurrentCaller.S1PrepareCode
