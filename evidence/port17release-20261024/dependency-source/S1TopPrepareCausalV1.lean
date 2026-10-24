import S1TopPrepareCodeV1
import S1CurrentPrepareCausalV1
import VTop_OracleCode
set_option autoImplicit false
noncomputable section
namespace AspisS1TopPrepareCode
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.PreparedHashCode
open AspisR1ClaimPreparedBridge AspisS1TopPrepareCarrier AspisS1TopPrepareSource
open AspisR1CurrentCaller.BorrowedClaimPrepared
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw
open S4SolanaDigestWrapperP3BindingV1

/-- Same emitted wrapper, Copy and digest operations at the top ABI. -/
def digest (sha : Bytes → Array U8 32#usize) : VTop_Stages.aspis_core.digest.Digest32 SolanaDigest :=
  {coremarkerCopyInst:=(p3CallerDigest sha).coremarkerCopyInst,digest:=(p3CallerDigest sha).digest}

theorem dictionary_irrelevant (base : AspisR1CurrentCaller.Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    {H : Type} (first second : VTop_Stages.aspis_core.digest.Digest32 H)
    (pub : VTop_Stages.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H) (input : Array Top.E 29#usize) :
    oracleProgram (code base R B first pub proof hash input)=
      oracleProgram (code base R B second pub proof hash input) := by
  unfold code
  apply oracleProgram_bind_congr
  · apply AspisR1CurrentCaller.S1PrepareCode.dictionary_irrelevant
  · intro result
    rfl

theorem p3_valid (base : AspisR1CurrentCaller.Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (sha : Bytes → Array U8 32#usize)
    (pub : VTop_Stages.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : SolanaDigest) (input : Array Top.E 29#usize) :
    OracleValid sha (code base R B (digest sha) pub proof hash input) := by
  unfold code
  apply valid_bind
  · exact AspisR1CurrentCaller.S1PrepareCode.p3_valid base R B sha _ proof hash _
  · intro result
    exact valid_pure sha _

def program (base : AspisR1CurrentCaller.Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (pub : VTop_Stages.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : SolanaDigest) (input : Array Top.E 29#usize) :=
  oracleProgram (code base R B (digest (fun _ => Array.repeat 32#usize 0#u8)) pub proof hash input)

/-- Fixed top op7 program, with the same complete Prepared/gamma scratch and
ordered read prefixes as its installed source body on every result. -/
theorem causal_exact (base : AspisR1CurrentCaller.Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (sha : Bytes → Array U8 32#usize)
    (pub : VTop_Stages.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : SolanaDigest) (input : Array Top.E 29#usize) :
    eval (fun bytes => decodeState (sha bytes)) (program base R B pub proof hash input)=
      (observe (run (code base R B (digest sha) pub proof hash input)).1,
        AspisS1TopPrepareSource.prepare (sourceOps base R B) (digest sha) pub proof hash none input) := by
  unfold program
  rw [dictionary_irrelevant base R B _ (digest sha)]
  rw [oracleProgram_exact sha _ (p3_valid base R B sha pub proof hash input),run_value,source]

/-- Concrete release op7 implementation. All other operations, and observer
Some calls, retain the supplied implementation. No whole-driver join is claimed. -/
def body (base : AspisR1CurrentCaller.Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (other : AspisR1.VTop_OracleCode.Implementation) : AspisR1.VTop_OracleCode.Implementation :=
  fun call => match call with
  | .op7 D pub proof hash none input => oracleProgram (code base R B D pub proof hash input)
  | call => other call

theorem installed (base : AspisR1CurrentCaller.Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (other : AspisR1.VTop_OracleCode.Implementation)
    {H : Type} (D : VTop_Stages.aspis_core.digest.Digest32 H)
    (pub : VTop_Stages.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H) (input : Array Top.E 29#usize) :
    body base R B other (.op7 D pub proof hash none input)=
      oracleProgram (code base R B D pub proof hash input) := rfl

theorem installed_effects (base : AspisR1CurrentCaller.Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (other : AspisR1.VTop_OracleCode.Implementation)
    (sha : Bytes → Array U8 32#usize)
    (pub : VTop_Stages.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : SolanaDigest) (input : Array Top.E 29#usize) :
    eval (fun bytes => decodeState (sha bytes))
      (body base R B other (.op7 (digest sha) pub proof hash none input))=
      (observe (run (code base R B (digest sha) pub proof hash input)).1,
        AspisS1TopPrepareSource.prepare (sourceOps base R B) (digest sha) pub proof hash none input) := by
  rw [installed,oracleProgram_exact sha _ (p3_valid base R B sha pub proof hash input),run_value,source]

#print axioms dictionary_irrelevant
#print axioms causal_exact
#print axioms installed
#print axioms installed_effects
end AspisS1TopPrepareCode
