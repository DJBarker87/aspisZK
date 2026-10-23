import VTop_Trace
import OraclePortFrozen2Join

/-! Oracle interpretation of the extracted typed call tree. All call arguments
and returned mutable state are retained. No identification with dV is assumed
or claimed. Ordinary inner Rust Err is a value of the dependent result type. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.VTop_OracleCode
open Aeneas Aeneas.Std Result VTop_Trace
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

abbrev Implementation := {A : Type} → Call A → Program Bytes State (Result A)

def continueWith {A B : Type} (r : Result A)
    (k : A → Program Bytes State (Result B)) : Program Bytes State (Result B) :=
  match r with
  | .ok a => k a
  | .fail e => .done (.fail e)
  | .div => .done .div

def interpret (impl : Implementation) {A : Type} : Code A → Program Bytes State (Result A)
  | .done a => .done (.ok a)
  | .step r k => continueWith r (fun a => interpret impl (k a))
  | .call op k => bind (impl op) (fun r => continueWith r (fun a => interpret impl (k a)))

/-- A local call law: complete ordered reads and the complete dependent return
are equal whenever that source call returns. This does not bind an arbitrary
Verifier to the tree, and does not identify a model implementation with dV. -/
def CallJoin (source model : Implementation) : Prop :=
  ∀ {A : Type} (call : Call A) (H : Bytes → State) (value : A),
    (eval H (source call)).2 = .ok value →
      eval H (source call) = eval H (model call)

/-- Symbolic substitution through the actual typed syntax, retaining source
branch selection and concatenation order. No large stage reduction is needed. -/
theorem accepted_interpret_eq (source model : Implementation) (joins : CallJoin source model)
    {A : Type} (tree : Code A) (H : Bytes → State) (value : A)
    (accepted : (eval H (interpret source tree)).2 = .ok value) :
    eval H (interpret source tree) = eval H (interpret model tree) := by
  induction tree with
  | done a => rfl
  | step r k ih =>
    cases r with
    | fail e => cases accepted
    | div => cases accepted
    | ok a => exact ih a accepted
  | call op k ih =>
    simp only [interpret, eval_bind] at accepted ⊢
    cases returned : (eval H (source op)).2 with
    | fail e => simp only [returned, continueWith, eval] at accepted; cases accepted
    | div => simp only [returned, continueWith, eval] at accepted; cases accepted
    | ok a =>
      have localJoin := joins op H a returned
      rw [← localJoin]
      simp only [returned, continueWith] at accepted ⊢
      rw [ih a accepted]

#print axioms accepted_interpret_eq
end AspisR1.VTop_OracleCode
end
