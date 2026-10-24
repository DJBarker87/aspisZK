import Port17RELEASE_Prepare
import Port17RELEASE_Control
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port17RELEASE_Driver
open Aeneas Aeneas.Std Result VTop_Stages VTop_Trace VTop_OracleCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open Port17RELEASE_Prepare

/-- Actual multiplicities of the still-unprovided delegated producers. -/
def remainingWeight (w : Nat → Nat) : Nat :=
  2*w 3+w 4+2*w 6+2*w 9+2*w 10+2*w 11+w 12+w 17+w 19

theorem weights (w : Nat → Nat) :
    Port16CUT_Cuts.delegatedWeight (weight w) = 115 + remainingWeight w := by
  simp only [Port16CUT_Cuts.delegatedWeight, weight, remainingWeight,
    Nat.reduceEqDiff, if_false, if_true]
  omega

/-- Actual saved-Vec stages; the concrete A prepare body supplies op7's count.
No successful prepare, accepted execution, or other-call zero cost is assumed. -/
theorem stages (ops : Ops) (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap)
    (base : AspisR1CurrentCaller.Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (other : Implementation)
    (w : Nat → Nat) (remaining : OtherBudgets other w)
    {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (semantic : Port1_Driver.Semantic) (pub proof : Slice U8) (H : Bytes → State) :
    (eval H (Port1_Driver.stages (implementation ops reserved unwrap base R B other)
      D hash semantic pub proof)).1.length ≤ 1161 + remainingWeight w := by
  have h := Port17RELEASE_Control.stages ops reserved unwrap
    (AspisS1TopPrepareCode.body base R B other) (weight w) (budgets base R B other w remaining)
    D hash semantic pub proof H
  rw [weights] at h
  exact h.trans (by omega)

theorem rust (ops : Ops) (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap)
    (base : AspisR1CurrentCaller.Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (other : Implementation)
    (w : Nat → Nat) (remaining : OtherBudgets other w)
    (adapter : AdapterRw.Ops) {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (hash : Hash) (H : Bytes → State) (i : OraclePortStoredExperimentC4.Input) :
    (eval H (Port1_Driver.rust adapter (implementation ops reserved unwrap base R B other)
      D hash i)).1.length ≤ 1161 + remainingWeight w := by
  have h := Port17RELEASE_Control.rust ops reserved unwrap
    (AspisS1TopPrepareCode.body base R B other) (weight w) (budgets base R B other w remaining)
    adapter D hash H i
  rw [weights] at h
  exact h.trans (by omega)

#print axioms weights
#print axioms stages
#print axioms rust
end AspisR1.Port17RELEASE_Driver
end
