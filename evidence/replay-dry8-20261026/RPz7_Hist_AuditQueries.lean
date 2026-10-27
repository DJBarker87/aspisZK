import Hist_P2Prime
import RPz7_SdkC_Replay
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hist_AuditQueries
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open AspisV8R19.CausalFirstHitUnionBound
open AspisV8PairedCommitment
abbrev Inputs := R9PoolRuntimeBinding.Inputs

/-- Four charged audit reads, appended after the containing source experiment.
These do not replace or reorder any source queries, including rejected ones. -/
def audit (written current : Inputs) : Program Bytes State Unit :=
  .ask written.proof fun _ => .ask written.pub fun _ =>
    .ask current.proof fun _ => .ask current.pub fun _ => .done ()

def augmented {A : Type} (source : Program Bytes State A)
    (select : A → Inputs × Inputs) : Program Bytes State A :=
  bind source fun value => bind (audit (select value).1 (select value).2) fun _ => .done value

theorem audit_eval (H : Bytes → State) (written current : Inputs) :
    eval H (audit written current) =
      ([(written.proof,H written.proof),(written.pub,H written.pub),
        (current.proof,H current.proof),(current.pub,H current.pub)],()) := rfl

theorem augmented_eval {A : Type} (H : Bytes → State) (source : Program Bytes State A)
    (select : A → Inputs × Inputs) :
    eval H (augmented source select) =
      ((eval H source).1 ++ (eval H (audit (select (eval H source).2).1
        (select (eval H source).2).2)).1,(eval H source).2) := by
  simp only [augmented,eval_bind,eval,List.append_nil,audit_eval]

theorem augmented_budget {A : Type} (source : Program Bytes State A)
    (select : A → Inputs × Inputs) (Q : Nat)
    (budget : ∀ H : Bytes → State, firstReads emptyTable (eval H source).1 ≤ Q)
    (H : Bytes → State) :
    firstReads emptyTable (eval H (augmented source select)).1 ≤ Q+4 := by
  rw [augmented_eval]
  exact (SdkC_Replay.firstReads_append_le _ _ _).trans
    (Nat.add_le_add (budget H) (by rw [audit_eval]; rfl))

#print axioms audit_eval
#print axioms augmented_eval
#print axioms augmented_budget
end AspisR1.Hist_AuditQueries
end
