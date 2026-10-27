import RPz7_GExp_LevelsBudget
import RPz7_GExp_CountTactic
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExp_VerifyBudget
open Aeneas Aeneas.Std Result CheckpointBytes5Effect GExp_CountLaws MultiproofConeRef
open MultiproofConeLevelIteration

theorem verify (root : Digest) (s : reference.Scratch) (physical : Slice U8) :
    count 288 (Port9OR_P6Verify.code root s physical) := by
  unfold Port9OR_P6Verify.code
  split
  · exact pure_count _ _
  · split
    · exact pure_count _ _
    · apply lift_bind_count; intro valid
      split
      · apply lift_bind_count; intro rem
        split
        · exact pure_count _ _
        · query_count_then_for 288 Port9OR_P6Levels.levels
          · decide
          · apply GExp_LevelsBudget.levels
            refine ⟨?_,?_,?_⟩ <;> scalar_tac
          · intro out
            exact lift_count _ _
      · exact pure_count _ _

#print axioms verify
end AspisR1.GExp_VerifyBudget
end
