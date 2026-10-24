import S1PrepareBudgetTacticV1
import S1SemanticCodeVerifyExactV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.S1SemanticCode
open Aeneas Aeneas.Std Result
open PreparedHashCode PreparedBudget
attribute [local irreducible] PreparedHashCode.effects

/-- Every source-code path, including rejection before the last read. -/
theorem sampleBlock_bounded  {H : Type} (D : aspis_core.Digest32 H)
    (self : r1_wire.SemanticTranscript H) (row : U8) (framed : Slice U8) : bounded 3 (sampleBlock D self row framed) := by
  unfold sampleBlock
  repeat' first
    | (solve | apply pure_bound)
    | (solve | apply lift_bound)
    | (apply lift_bind;intro x)
    | (budget_then 1
       <;> first | omega | (solve | exact digest_bound _ _ _) | intro x)
    | split

attribute [local irreducible] sampleBlock

/-- Every source-code path, including rejection before the last read. -/
theorem semanticValidated_bounded  {H : Type} (D : aspis_core.Digest32 H)
    (self : r1_wire.SemanticTranscript H) (record1 : r1_wire.ValidatedRecord) : bounded 3 (semanticValidated D self record1) := by
  unfold semanticValidated
  repeat' first
    | (solve | apply pure_bound)
    | (solve | apply lift_bound)
    | (apply mono (n:=3)
       <;> first | omega | (solve | apply sampleBlock_bounded))
    | (budget_then 3
       <;> first | omega | (solve | apply sampleBlock_bounded) | intro x)
    | (apply lift_bind;intro x)
    | (budget_then 1
       <;> first | omega | (solve | exact digest_bound _ _ _) | intro x)
    | split

attribute [local irreducible] semanticValidated

/-- Every source-code path, including rejection before the last read. -/
theorem begin13_bounded  {H : Type} (D : aspis_core.Digest32 H)
    (prefix1 : r1_wire.Prefix) (transcript13 : r1_wire.SemanticTranscript H)
    (val val1 val2 val12 : aspis_core.field.QM31)
    (index_mut_back9 : aspis_core.field.QM31 → Array aspis_core.field.QM31 10#usize) : bounded 6 (begin13 D prefix1 transcript13 val val1 val2 val12 index_mut_back9) := by
  unfold begin13
  repeat' first
    | (solve | apply pure_bound)
    | (solve | apply lift_bound)
    | (apply mono (n:=3)
       <;> first | omega | (solve | apply semanticValidated_bounded))
    | (budget_then 3
       <;> first | omega | (solve | apply semanticValidated_bounded) | intro x)
    | (apply lift_bind;intro x)
    | (budget_then 1
       <;> first | omega | (solve | exact digest_bound _ _ _) | intro x)
    | split

attribute [local irreducible] begin13

/-- Every source-code path, including rejection before the last read. -/
theorem begin9_bounded  {H : Type} (D : aspis_core.Digest32 H)
    (prefix1 : r1_wire.Prefix) (transcript9 : r1_wire.SemanticTranscript H)
    (val val1 val2 val8 : aspis_core.field.QM31)
    (index_mut_back5 : aspis_core.field.QM31 → Array aspis_core.field.QM31 10#usize) : bounded 18 (begin9 D prefix1 transcript9 val val1 val2 val8 index_mut_back5) := by
  unfold begin9
  repeat' first
    | (solve | apply pure_bound)
    | (solve | apply lift_bound)
    | (apply mono (n:=3)
       <;> first | omega | (solve | apply semanticValidated_bounded))
    | (budget_then 3
       <;> first | omega | (solve | apply semanticValidated_bounded) | intro x)
    | (apply mono (n:=6)
       <;> first | omega | (solve | apply begin13_bounded))
    | (budget_then 6
       <;> first | omega | (solve | apply begin13_bounded) | intro x)
    | (apply lift_bind;intro x)
    | (budget_then 1
       <;> first | omega | (solve | exact digest_bound _ _ _) | intro x)
    | split

attribute [local irreducible] begin9

/-- Every source-code path, including rejection before the last read. -/
theorem begin5_bounded  {H : Type} (D : aspis_core.Digest32 H)
    (prefix1 : r1_wire.Prefix) (transcript5 : r1_wire.SemanticTranscript H)
    (val val1 val2 val4 : aspis_core.field.QM31)
    (index_mut_back1 : aspis_core.field.QM31 → Array aspis_core.field.QM31 10#usize) : bounded 30 (begin5 D prefix1 transcript5 val val1 val2 val4 index_mut_back1) := by
  unfold begin5
  repeat' first
    | (solve | apply pure_bound)
    | (solve | apply lift_bound)
    | (apply mono (n:=3)
       <;> first | omega | (solve | apply semanticValidated_bounded))
    | (budget_then 3
       <;> first | omega | (solve | apply semanticValidated_bounded) | intro x)
    | (apply mono (n:=18)
       <;> first | omega | (solve | apply begin9_bounded))
    | (budget_then 18
       <;> first | omega | (solve | apply begin9_bounded) | intro x)
    | (apply lift_bind;intro x)
    | (budget_then 1
       <;> first | omega | (solve | exact digest_bound _ _ _) | intro x)
    | split

attribute [local irreducible] begin5

/-- Every source-code path, including rejection before the last read. -/
theorem begin_bounded  {H : Type} (D : aspis_core.Digest32 H)
    (prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H) : bounded 45 (begin D prefix1 transcript) := by
  unfold begin
  repeat' first
    | (solve | apply pure_bound)
    | (solve | apply lift_bound)
    | (apply mono (n:=3)
       <;> first | omega | (solve | apply semanticValidated_bounded))
    | (budget_then 3
       <;> first | omega | (solve | apply semanticValidated_bounded) | intro x)
    | (apply mono (n:=30)
       <;> first | omega | (solve | apply begin5_bounded))
    | (budget_then 30
       <;> first | omega | (solve | apply begin5_bounded) | intro x)
    | (apply lift_bind;intro x)
    | (budget_then 1
       <;> first | omega | (solve | exact digest_bound _ _ _) | intro x)
    | split

attribute [local irreducible] begin

/-- Every source-code path, including rejection before the last read. -/
theorem newTranscript_bounded  {H : Type} (D : aspis_core.Digest32 H)
    (hash : H) (publicBytes : Slice U8) (root : Array U8 32#usize) : bounded 1 (newTranscript D hash publicBytes root) := by
  unfold newTranscript
  repeat' first
    | (solve | apply pure_bound)
    | (solve | apply lift_bound)
    | (apply lift_bind;intro x)
    | (budget_then 1
       <;> first | omega | (solve | exact digest_bound _ _ _) | intro x)
    | split

attribute [local irreducible] newTranscript

/-- Every source-code path, including rejection before the last read. -/
theorem publicTranscript_bounded  {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (hash : H) (root : Array U8 32#usize) : bounded 1 (publicTranscript D pub hash root) := by
  unfold publicTranscript
  repeat' first
    | (solve | apply pure_bound)
    | (solve | apply lift_bound)
    | (apply mono (n:=1)
       <;> first | omega | (solve | apply newTranscript_bounded))
    | (budget_then 1
       <;> first | omega | (solve | apply newTranscript_bounded) | intro x)
    | (apply lift_bind;intro x)
    | (budget_then 1
       <;> first | omega | (solve | exact digest_bound _ _ _) | intro x)
    | split

attribute [local irreducible] publicTranscript

/-- Every source-code path, including rejection before the last read. -/
theorem roundStep_bounded (B : RoundModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H)
    (alpha : Array aspis_core.field.QM31 10#usize) (running : aspis_core.field.QM31) (round : Usize) : bounded 3 (roundStep B D prefix1 transcript alpha running round) := by
  unfold roundStep
  repeat' first
    | (solve | apply pure_bound)
    | (solve | apply lift_bound)
    | (apply mono (n:=3)
       <;> first | omega | (solve | apply semanticValidated_bounded))
    | (budget_then 3
       <;> first | omega | (solve | apply semanticValidated_bounded) | intro x)
    | (apply lift_bind;intro x)
    | (budget_then 1
       <;> first | omega | (solve | exact digest_bound _ _ _) | intro x)
    | split

attribute [local irreducible] roundStep

/-- Every source-code path, including rejection before the last read. -/
theorem rounds_bounded (B : RoundModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H) : bounded 30 (rounds B D prefix1 transcript) := by
  unfold rounds
  repeat' first
    | (solve | apply pure_bound)
    | (solve | apply lift_bound)
    | (apply mono (n:=3)
       <;> first | omega | (solve | apply roundStep_bounded))
    | (budget_then 3
       <;> first | omega | (solve | apply roundStep_bounded) | intro x)
    | (apply lift_bind;intro x)
    | (budget_then 1
       <;> first | omega | (solve | exact digest_bound _ _ _) | intro x)
    | split

attribute [local irreducible] rounds

/-- Every source-code path, including rejection before the last read. -/
theorem circleValidated_bounded (B : FinishModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (self : r1_wire.SemanticTranscript H) (record1 : r1_wire.ValidatedRecord) : bounded 3 (circleValidated B D self record1) := by
  unfold circleValidated
  repeat' first
    | (solve | apply pure_bound)
    | (solve | apply lift_bound)
    | (apply mono (n:=3)
       <;> first | omega | (solve | apply sampleBlock_bounded))
    | (budget_then 3
       <;> first | omega | (solve | apply sampleBlock_bounded) | intro x)
    | (apply lift_bind;intro x)
    | (budget_then 1
       <;> first | omega | (solve | exact digest_bound _ _ _) | intro x)
    | split

attribute [local irreducible] circleValidated

/-- Every source-code path, including rejection before the last read. -/
theorem finish_bounded (R : RoundModel.Boundaries) (B : FinishModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (prefix1 : r1_wire.Prefix)
    (transcript : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges)
    (obs : Option (verifier.Phase → Result Unit)) : bounded 36 (finish R B D pub prefix1 transcript challenges obs) := by
  unfold finish
  repeat' first
    | (solve | apply pure_bound)
    | (solve | apply lift_bound)
    | (apply mono (n:=30)
       <;> first | omega | (solve | apply rounds_bounded))
    | (budget_then 30
       <;> first | omega | (solve | apply rounds_bounded) | intro x)
    | (apply mono (n:=3)
       <;> first | omega | (solve | apply circleValidated_bounded))
    | (budget_then 3
       <;> first | omega | (solve | apply circleValidated_bounded) | intro x)
    | (apply lift_bind;intro x)
    | (budget_then 1
       <;> first | omega | (solve | exact digest_bound _ _ _) | intro x)
    | split

attribute [local irreducible] finish

/-- Every source-code path, including rejection before the last read. -/
theorem verify_bounded (R : RoundModel.Boundaries) (B : FinishModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (bytes : Slice U8) (hash : H)
    (obs : Option (verifier.Phase → Result Unit)) : bounded 82 (verify (finish R B) D pub bytes hash obs) := by
  unfold verify
  repeat' first
    | (solve | apply pure_bound)
    | (solve | apply lift_bound)
    | (apply mono (n:=1)
       <;> first | omega | (solve | apply publicTranscript_bounded))
    | (budget_then 1
       <;> first | omega | (solve | apply publicTranscript_bounded) | intro x)
    | (apply mono (n:=45)
       <;> first | omega | (solve | apply begin_bounded))
    | (budget_then 45
       <;> first | omega | (solve | apply begin_bounded) | intro x)
    | (apply mono (n:=36)
       <;> first | omega | (solve | apply finish_bounded))
    | (budget_then 36
       <;> first | omega | (solve | apply finish_bounded) | intro x)
    | (apply lift_bind;intro x)
    | (budget_then 1
       <;> first | omega | (solve | exact digest_bound _ _ _) | intro x)
    | split

attribute [local irreducible] verify

#print axioms sampleBlock_bounded
#print axioms semanticValidated_bounded
#print axioms begin13_bounded
#print axioms begin9_bounded
#print axioms begin5_bounded
#print axioms begin_bounded
#print axioms newTranscript_bounded
#print axioms publicTranscript_bounded
#print axioms roundStep_bounded
#print axioms rounds_bounded
#print axioms circleValidated_bounded
#print axioms finish_bounded
#print axioms verify_bounded
end AspisR1PublicPreparation.S1SemanticCode
