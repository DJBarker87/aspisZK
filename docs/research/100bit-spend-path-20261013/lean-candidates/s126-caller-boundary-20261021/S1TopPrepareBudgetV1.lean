import S1CurrentPrepareBudgetV1
import S1TopPrepareOracleV1
set_option autoImplicit false
noncomputable section
namespace AspisS1TopPrepareCode
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.PreparedHashCode AspisR1PublicPreparation.PreparedBudget
open AspisS1TopPrepareCarrier
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw
open S4SolanaDigestWrapperP3BindingV1

theorem code_bounded (base : AspisR1CurrentCaller.Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash)
    (pub : VTop_Stages.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : Hash) (input : Array Top.E 29#usize) :
    bounded 115 (code base R B D pub proof hash input) := by
  unfold code
  budget_then 115
  · omega
  · exact AspisR1CurrentCaller.S1PrepareCode.prepare_bounded _ _ _ _ _ _ _ _
  · intro result
    cases result
    exact pure_bound _ _

/-- Fixed reply-driven Program, all oracles and complete rejection prefixes. -/
theorem program_count (base : AspisR1CurrentCaller.Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (H : Bytes → State)
    (pub : VTop_Stages.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : SolanaDigest) (input : Array Top.E 29#usize) :
    (eval H (program base R B pub proof hash input)).1.length ≤ 115 := by
  exact count _ H 115 (code_bounded _ _ _ _ _ _ _ _)

/-- The count holds at the complete installed release op7 ABI, for arbitrary
D and H. This bound alone does not identify native D with H. -/
theorem installed_count (base : AspisR1CurrentCaller.Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (other : AspisR1.VTop_OracleCode.Implementation) (H : Bytes → State)
    {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash)
    (pub : VTop_Stages.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : Hash) (input : Array Top.E 29#usize) :
    (eval H (body base R B other (.op7 D pub proof hash none input))).1.length ≤ 115 := by
  rw [installed]
  exact count _ H 115 (code_bounded _ _ _ _ _ _ _ _)

/-- The same complete source evaluation supplies BOTH effects/value equality
and its bound. No independently assumed trace, success or count is required. -/
theorem installed_effects_count (base : AspisR1CurrentCaller.Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (other : AspisR1.VTop_OracleCode.Implementation) (H : Bytes → State)
    (pub : VTop_Stages.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : SolanaDigest) (input : Array Top.E 29#usize) :
    eval H (body base R B other
      (.op7 (digest (fun bytes => encodeState (H bytes))) pub proof hash none input))=
      (observe (run (code base R B (digest (fun bytes => encodeState (H bytes))) pub proof hash input)).1,
        AspisS1TopPrepareSource.prepare (sourceOps base R B) (digest (fun bytes => encodeState (H bytes)))
          pub proof hash none input) ∧
    (eval H (body base R B other
      (.op7 (digest (fun bytes => encodeState (H bytes))) pub proof hash none input))).1.length ≤ 115 :=
  ⟨installed_oracle base R B other H pub proof hash input,
    installed_count base R B other H _ pub proof hash input⟩

#print axioms code_bounded
#print axioms program_count
#print axioms installed_count
#print axioms installed_effects_count
end AspisS1TopPrepareCode
