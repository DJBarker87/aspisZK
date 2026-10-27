import ARS_QueryTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARS_WorldCylinder
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

/-- Equality of complete recorded executions entails agreement at every read.
This proves the ruling's execution-cylinder statement without asserting that
this cylinder has unconditional probability one. -/
theorem reads_consistent {I S X : Type} (H : I → S) (p : Program I S X) :
    ∀ q ∈ (eval H p).1, q.2 = H q.1 := by
  induction p with
  | done value => intro q member; cases member
  | ask address next ih =>
    intro q member
    rcases List.mem_cons.mp member with head | tail
    · subst q
      rfl
    · exact ih (H address) q tail

theorem agrees_of_same {I S X : Type} (native H : I → S) (p : Program I S X)
    (same : eval H p = eval native p) :
    ∀ address ∈ (eval native p).1.map Prod.fst, H address = native address := by
  intro address member
  obtain ⟨q,belongs,at⟩ := List.mem_map.mp member
  have left := reads_consistent native p q belongs
  have right := reads_consistent H p q (by rw [same]; exact belongs)
  rw [← at]
  exact right.symm.trans left

/-- The exact set of worlds in which this complete execution occurs. -/
theorem iff_same {I S X : Type} [DecidableEq I]
    (native H : I → S) (p : Program I S X) :
    (∀ address ∈ (eval native p).1.map Prod.fst, H address = native address) ↔
      eval H p = eval native p :=
  ⟨OracleProgramReplay.eval_eq_of_agrees native H p,agrees_of_same native H p⟩

/-- One differing issued answer is a different recorded execution. -/
theorem different_execution {I S X : Type} (native H : I → S) (p : Program I S X)
    (address : I) (issued : address ∈ (eval native p).1.map Prod.fst)
    (different : H address ≠ native address) : eval H p ≠ eval native p := by
  intro same
  exact different (agrees_of_same native H p same address issued)

#print axioms reads_consistent
#print axioms agrees_of_same
#print axioms iff_same
#print axioms different_execution
end AspisR1.ARS_WorldCylinder
end
