import Port16CUT_Driver
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port17RELEASE_Domain
open Aeneas Aeneas.Std Result VTop_Stages VTop_Trace VTop_OracleCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- Release observer domain. No restriction on input or child result. -/
def ReleaseCall {A : Type} : Call A → Prop
  | .op6 _ _ _ _ observer _ _ _ => observer = none
  | .op7 _ _ _ _ observer _ => observer = none
  | .op19 _ _ _ observer => observer = none
  | _ => True

/-- Every continuation, including values never returned by an implementation. -/
def CallsIn {A : Type} : Code A → Prop
  | .done _ => True
  | .step _ k => ∀ b, CallsIn (k b)
  | .call op k => ReleaseCall op ∧ ∀ b, CallsIn (k b)

def ReleaseBudgets (rest : Implementation) (w : Nat → Nat) : Prop :=
  ∀ {A : Type} (op : Call A) (H : Bytes → State),
    operationId op ∈ Port15DRIVER_Local.delegatedIds → ReleaseCall op →
      (eval H (rest op)).1.length ≤ w (operationId op)

theorem old_implies_release (rest : Implementation) (w : Nat → Nat)
    (h : Port15DRIVER_Local.LocalBudgets rest w) : ReleaseBudgets rest w :=
  fun op H member _ => h op H member

theorem delegated (ops : Ops) (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap)
    (rest : Implementation) (w : Nat → Nat) (budgets : ReleaseBudgets rest w)
    {A : Type} (op : Call A) (H : Bytes → State)
    (member : operationId op ∈ Port15DRIVER_Local.delegatedIds) (domain : ReleaseCall op) :
    (eval H (Port9OR_Installed.implementation ops reserved unwrap rest op)).1.length ≤ w (operationId op) := by
  have same : Port9OR_Installed.implementation ops reserved unwrap rest op = rest op := by
    cases op <;> simp_all only [operationId, Port15DRIVER_Local.delegatedIds, List.mem_cons,
      List.not_mem_nil, or_false, Nat.reduceEqDiff, or_self]
    all_goals rfl
  rw [same]
  exact budgets op H member domain

#print axioms old_implies_release
#print axioms delegated
end AspisR1.Port17RELEASE_Domain
end
