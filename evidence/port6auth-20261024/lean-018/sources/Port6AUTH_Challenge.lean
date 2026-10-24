import OraclePortFrozenOrderSlot
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port6AUTH_Challenge
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortFrozenOrder

/-- Exact source leaf-scan boundary challenge: in a constant oracle world,
changing ALL opening bytes cannot affect its returned digest frontier. This
covers any queries, including distinct queries with repeated folded parents.
It does NOT assert full verifier acceptance, parser validity or a join failure. -/
theorem frontier_independent (z : State) (p p' : Parsed)
    (q : Fin 22 → Fin 262144) (kind : Nat) (ps : List Nat) (rev : Live) :
    (eval (fun _ => z) (hashLeaves p q kind ps rev)).2=
      (eval (fun _ => z) (hashLeaves p' q kind ps rev)).2 := by
  induction ps generalizing rev with
  | nil => rfl
  | cons pos rest ih =>
    cases rev with
    | nil => exact ih _
    | cons entry tail =>
      rcases entry with ⟨j,v⟩
      simp only [hashLeaves,eval]
      split
      · split
        · exact ih _
        · rfl
      · exact ih _

/-- Applies to both complete batch position schedules and stable sorting,
without reducing either ten/twelve-entry scan. -/
theorem both_batches (z : State) (p p' : Parsed) (q : Fin 22 → Fin 262144) :
    ∀ b : Fin 2, (eval (fun _ => z) (hashLeaves p q 2 (sortedPositions q b.val 2) [])).2=
      (eval (fun _ => z) (hashLeaves p' q 2 (sortedPositions q b.val 2) [])).2 := by
  intro b
  exact frontier_independent z p p' q 2 _ []

#print axioms frontier_independent
#print axioms both_batches
end AspisR1.Port6AUTH_Challenge
end
