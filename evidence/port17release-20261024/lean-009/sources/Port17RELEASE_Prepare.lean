import Port17RELEASE_Domain
import S1TopPrepareBudgetV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port17RELEASE_Prepare
open Aeneas Aeneas.Std Result VTop_Stages VTop_Trace VTop_OracleCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open Port17RELEASE_Domain

/-- Exact remaining per-call obligations, with no op7 count premise. -/
def OtherBudgets (other : Implementation) (w : Nat → Nat) : Prop :=
  ∀ {A : Type} (op : Call A) (H : Bytes → State),
    operationId op ∈ Port15DRIVER_Local.delegatedIds → operationId op ≠ 7 →
      ReleaseCall op → (eval H (other op)).1.length ≤ w (operationId op)

def weight (w : Nat → Nat) (id : Nat) : Nat := if id = 7 then 115 else w id

def implementation (ops : Ops) (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap)
    (base : AspisR1CurrentCaller.Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (other : Implementation) : Implementation :=
  Port9OR_Installed.implementation ops reserved unwrap (AspisS1TopPrepareCode.body base R B other)

theorem op7_count (ops : Ops) (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap)
    (base : AspisR1CurrentCaller.Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (other : Implementation)
    {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : Hash)
    (input : Array aspis_core.field.wide_exact.WideExact 29#usize) (H : Bytes → State) :
    (eval H (implementation ops reserved unwrap base R B other
      (.op7 D pub proof hash none input))).1.length ≤ 115 := by
  exact AspisS1TopPrepareCode.installed_count base R B other H D pub proof hash input

theorem body_other (base : AspisR1CurrentCaller.Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (other : Implementation)
    {A : Type} (op : Call A) (not7 : operationId op ≠ 7) :
    AspisS1TopPrepareCode.body base R B other op = other op := by
  cases op <;> simp_all only [operationId, Nat.reduceEqDiff]
  all_goals rfl

theorem budgets (base : AspisR1CurrentCaller.Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (other : Implementation)
    (w : Nat → Nat) (remaining : OtherBudgets other w) :
    ReleaseBudgets (AspisS1TopPrepareCode.body base R B other) (weight w) := by
  intro A op H member domain
  by_cases seven : operationId op = 7
  · cases op <;> simp_all only [operationId, Nat.reduceEqDiff]
    case op7 D pub proof hash observer input =>
      have observerNone : observer = none := domain
      subst observer
      exact AspisS1TopPrepareCode.installed_count base R B other H D pub proof hash input
  · rw [body_other base R B other op seven]
    simpa only [weight, if_neg seven] using remaining op H member seven domain

#print axioms op7_count
#print axioms body_other
#print axioms budgets
end AspisR1.Port17RELEASE_Prepare
end
