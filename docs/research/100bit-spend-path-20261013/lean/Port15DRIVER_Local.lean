import Port15DRIVER_Cost
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port15DRIVER_Local
open Aeneas Aeneas.Std Result VTop_Stages VTop_Trace VTop_OracleCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

def delegatedIds : List Nat := [3,4,6,7,9,10,11,12,17,19]
/-- Only individual delegated calls, on every argument and outcome. -/
def LocalBudgets (rest : Implementation) (w : Nat → Nat) : Prop :=
  ∀ {A : Type} (op : Call A) (H : Bytes → State),
    operationId op ∈ delegatedIds → (eval H (rest op)).1.length ≤ w (operationId op)

theorem delegated (ops : Ops) (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap)
    (rest : Implementation) (w : Nat → Nat) (budgets : LocalBudgets rest w)
    {A : Type} (op : Call A) (H : Bytes → State)
    (member : operationId op ∈ delegatedIds) :
    (eval H (Port9OR_Installed.implementation ops reserved unwrap rest op)).1.length ≤ w (operationId op) := by
  have same : Port9OR_Installed.implementation ops reserved unwrap rest op = rest op := by
    cases op <;> simp_all only [operationId, delegatedIds, List.mem_cons,
      List.not_mem_nil, or_false, Nat.reduceEqDiff, or_self]
    all_goals rfl
  rw [same]
  exact budgets op H member

theorem library (ops : Ops) (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap)
    (rest : Implementation) {A : Type} (op : Call A) (H : Bytes → State)
    (member : operationId op ∈ VTop_OracleStages.libraryIds) :
    (eval H (Port9OR_Installed.implementation ops reserved unwrap rest op)).1.length ≤ 0 := by
  rw [Port9OR_Installed.implementation, Port9OR_Bodies.implementation,
    Port1_Library.library_no_read _ _ _ member]
  exact Nat.zero_le _

#print axioms delegated
#print axioms library
end AspisR1.Port15DRIVER_Local
end
