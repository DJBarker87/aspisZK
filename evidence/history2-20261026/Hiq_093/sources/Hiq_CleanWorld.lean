import Hiq_RecordedBudget
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_CleanWorld
open FS FS2 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.CausalFirstHitUnionBound

/-- Non-collision worlds exist without conditioning on an unproved acceptance
probability. This does NOT assert an accepted cryptographic fixture. -/
theorem exists_clean {A : Type} (program : Program Bytes State A) (bad : View Bytes State A → Prop)
    (small : lazyMean program emptyTable (fun v => indicator (bad v)) < 1) :
    ∃ H : Bytes → State, ¬ bad (eval H program) := by
  classical
  by_contra none
  have all : ∀ H : Bytes → State, bad (eval H program) := by simpa only [not_exists,not_not] using none
  have equal := OracleProgramLawExt.lazyMean_eq_of_eval program (.done ()) (fun v => indicator (bad v))
    (fun _ => (1:Rat)) (fun H => by simp only [indicator,if_pos (all H)])
  have constant : lazyMean (.done () : Program Bytes State Unit) emptyTable (fun _ => (1:Rat)) = 1 := rfl
  rw [constant] at equal
  linarith

#print axioms exists_clean
end AspisR1.Hiq_CleanWorld
end
