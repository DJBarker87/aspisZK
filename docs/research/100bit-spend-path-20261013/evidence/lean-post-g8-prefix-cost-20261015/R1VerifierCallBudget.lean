import FS2.Statement
import AspisV8R19.DuplexFrames

/-! Post-G8 SHA call budgets and a source-count interface.
The selected verifier uses one create_program_address per stored bump, with
at most seven calls in the immutable deployment branch or five in V1.
Only arithmetic and generic first-read bookkeeping are proved here. The
separate VerifierPhaseCost module proves an operational model's prefix bound.
Source/runtime refinement and trace completeness remain OPEN. -/
set_option autoImplicit false
namespace AspisR1.VerifierCallBudget

abbrev Bytes := AspisV8R19.DuplexFrames.Bytes
abbrev Digest := Fin 32 → AspisV8R19.DuplexFrames.Byte
abbrev Trace := List (Bytes × Digest)

/-- `running` includes suspension at any finite prefix before a later exit. -/
inductive PrefixStop where
  | running | accepted | rejected | panic | allocationFailure
  | computeExhausted | runtimeFailure

/-- Supplied independently from the budget: every designated digest evaluation,
including repeated inputs and each single-attempt PDA digest, contributes one trace entry.
`Input` must retain all invocation data, accounts and relevant initial state. -/
abbrev PrefixRelation (Cfg Input : Type) :=
  Cfg → Input → (Bytes → Digest) → PrefixStop → Trace → Prop

def PrefixClosed {Cfg Input : Type}
    (SourcePrefix : PrefixRelation Cfg Input) : Prop :=
  ∀ cfg input H stop pre post,
    SourcePrefix cfg input H stop (pre ++ post) →
    SourcePrefix cfg input H .running pre

/-- `Admitted` pins the configuration and release route. It must not assume
acceptance, a genuine checkpoint, or absence of an eventual runtime failure. -/
def AllPrefixCount {Cfg Input : Type}
    (SourcePrefix : PrefixRelation Cfg Input)
    (Admitted : Cfg → Input → Prop) (Q : Nat) : Prop :=
  ∀ cfg input H stop tr,
    Admitted cfg input → SourcePrefix cfg input H stop tr → tr.length ≤ Q

-- Proposed source caps; their correspondence with execution is not proved.
def semanticBudget : Nat := 1 + 27 * 3
def openingBudget : Nat := 1 + 4 * 3 + (1 + 8 * 2) + 3
def queryBudget : Nat := 3 + 3 * 6
def stage1Budget (k : Nat) : Nat :=
  semanticBudget + openingBudget + queryBudget * k + 3
def stage2CoreBudget : Nat := 3 + queryBudget * 22
def immutablePdaBudget : Nat := 7
def v1PdaBudget : Nat := 5
def stage2Budget : Nat := stage2CoreBudget + immutablePdaBudget
def stage2V1Budget : Nat := stage2CoreBudget + v1PdaBudget
def verifierBudget : Nat := max (stage1Budget 11) stage2Budget

theorem stage1Budget_ten : stage1Budget 10 = 328 := rfl
theorem stage1Budget_eleven : stage1Budget 11 = 349 := rfl
theorem stage2CoreBudget_value : stage2CoreBudget = 465 := rfl
theorem stage2Budget_value : stage2Budget = 472 := rfl
theorem stage2V1Budget_value : stage2V1Budget = 470 := rfl
theorem verifierBudget_value : verifierBudget = 472 := rfl

/-- OPEN integration obligation, parameterized by the actual source/runtime
relation. There is deliberately no proof or axiom asserting this obligation. -/
def SourceCountObligation {Cfg Input : Type}
    (SourcePrefix : PrefixRelation Cfg Input)
    (Admitted : Cfg → Input → Prop) : Prop :=
  PrefixClosed SourcePrefix ∧ AllPrefixCount SourcePrefix Admitted verifierBudget

/-- Generic bookkeeping, valid for arbitrary address types without a finite
address universe or a global input-length cap. -/
theorem firstReads_le_length {I A : Type} [DecidableEq I]
    (t : AspisV8PairedCommitment.Table I A) (tr : List (I × A)) :
    FS.firstReads t tr ≤ tr.length := by
  induction tr generalizing t with
  | nil => simp [FS.firstReads]
  | cons q rest ih =>
    rcases q with ⟨i, a⟩
    have h := ih (AspisV8PairedCommitment.put t i a)
    simp only [FS.firstReads, List.length_cons]
    split <;> omega

theorem distinctFirstReads_le_totalCalls {Pf : Type}
    (v : AspisV8R19.MemoizedProgramLaw.View Bytes Digest (Pf × Bool)) :
    FS2.distinctFirstReads v ≤ v.1.length := by
  exact firstReads_le_length FS.emptyTable v.1

theorem distinctFirstReads_of_totalCalls {Pf : Type}
    (v : AspisV8R19.MemoizedProgramLaw.View Bytes Digest (Pf × Bool))
    (Q : Nat) (h : v.1.length ≤ Q) : FS2.distinctFirstReads v ≤ Q :=
  Nat.le_trans (distinctFirstReads_le_totalCalls v) h

#print axioms stage1Budget_ten
#print axioms stage1Budget_eleven
#print axioms stage2CoreBudget_value
#print axioms stage2Budget_value
#print axioms stage2V1Budget_value
#print axioms verifierBudget_value
#print axioms firstReads_le_length
#print axioms distinctFirstReads_le_totalCalls
#print axioms distinctFirstReads_of_totalCalls

end AspisR1.VerifierCallBudget
