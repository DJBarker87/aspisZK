import RPz7_GExp_CountLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExp_LevelsBudget
open Aeneas Aeneas.Std Result CheckpointBytes5Effect MultiproofConeRef
open MultiproofConeLevelIteration
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem level (s : reference.Scratch) (physical : Slice U8) (small : s.n.val ≤ 16) :
    GExp_CountLaws.count 16 (Port9OR_P6Levels.level s physical) := by
  intro H
  exact (GExp_QueryBudget.program_count _ _ (GExp_RowsBudget.rows s.n.val s physical _ _) H).trans small

theorem levels (height : Nat) (s : reference.Scratch) (physical : Slice U8)
    (domain : Domain physical s) :
    GExp_CountLaws.count (16*height) (Port9OR_P6Levels.levels height s physical) := by
  induction height generalizing s with
  | zero => intro H; exact Nat.zero_le _
  | succ height ih =>
    intro H
    have first := level s physical domain.2.1 H
    have rest : ∀ out, (eval H (SdkC_Oracle.program (Port9OR_P6Levels.level s physical))).2 = ok out →
        (eval H (SdkC_Oracle.program (match out with
          | .Stop stopped => pure (.Stop stopped)
          | .Done next => Port9OR_P6Levels.levels height next physical))).1.length ≤ 16*height := by
      intro out ran
      cases out with
      | Stop stopped => exact Nat.zero_le _
      | Done next =>
        have actual := (GExp_IdealValue.value H (Port9OR_P6Levels.level s physical)).symm.trans ran
        rw [Port9OR_P6Levels.level_source _ () s physical domain] at actual
        have nextDomain := Port9OR_P6Levels.level_preserve (GExp_IdealValue.dictionary H) () s next physical domain actual
        exact ih next nextDomain H
    have bound := GExp_CountLaws.bind_count_on (Port9OR_P6Levels.level s physical) _ H 16 (16*height) first rest
    change (eval H (SdkC_Oracle.program (CheckpointBytes5Effect.bind
      (Port9OR_P6Levels.level s physical) _))).1.length ≤ _
    exact bound.trans (by omega)

#print axioms level
#print axioms levels
end AspisR1.GExp_LevelsBudget
end
