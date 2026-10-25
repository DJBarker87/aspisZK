import Port12COUNT_Installed
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port15DRIVER_Cost
open Aeneas Aeneas.Std Result VTop_Stages VTop_Trace VTop_OracleCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- A list of per-site allowances, consumed in actual source order. -/
def Fits (impl : Implementation) (H : Bytes → State) {A : Type}
    (tree : Code A) (sites : List Nat) : Prop :=
  (eval H (interpret impl tree)).1.length ≤ sites.sum

theorem done {A : Type} (impl : Implementation) (H : Bytes → State)
    (a : A) (sites : List Nat) : Fits impl H (.done a) sites := Nat.zero_le _

theorem step {A B : Type} (impl : Implementation) (H : Bytes → State)
    (r : Result B) (k : B → Code A) (sites : List Nat)
    (tail : ∀ b, Fits impl H (k b) sites) : Fits impl H (.step r k) sites := by
  cases r with
  | fail e => exact Nat.zero_le _
  | div => exact Nat.zero_le _
  | ok b => exact tail b

theorem call {A B : Type} (impl : Implementation) (H : Bytes → State)
    (op : Call B) (k : B → Code A) (n : Nat) (sites : List Nat)
    (localCost : (eval H (impl op)).1.length ≤ n)
    (tail : ∀ b, Fits impl H (k b) sites) : Fits impl H (.call op k) (n::sites) := by
  unfold Fits
  simp only [interpret, eval_bind, List.length_append, List.sum_cons]
  have remaining : (eval H (continueWith (eval H (impl op)).2
      (fun a => interpret impl (k a)))).1.length ≤ sites.sum := by
    cases (eval H (impl op)).2 with
    | fail e => exact Nat.zero_le _
    | div => exact Nat.zero_le _
    | ok b => exact tail b
  omega

#print axioms done
#print axioms step
#print axioms call
end AspisR1.Port15DRIVER_Cost
end
