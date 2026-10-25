import Port9OR_BatchStep

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port9OR_BatchProgress
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open Port9OR_BatchStep (Indices Values Next Out)

/-- Every ACTUAL source continuation advances the actual key cursor. No
assumption about key contents, sortedness, hash totality or acceptance. -/
theorem advance (base : Port3_NativeBatchBody.Ops) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (proof : Slice U8) (root : Array U8 32#usize) (tree lo n slot : Usize)
    (keys : Array U64 16#usize) (idx : Indices) (val : Values) (d pos : Usize)
    (nextIdx : Indices) (nextVal : Values) (nextD nextPos : Usize)
    (ran : Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port9OR_BatchStep.ops base) D proof root tree hash lo n slot keys idx val d pos=
        ok (.cont (nextIdx,nextVal,nextD,nextPos))) :
    pos<n ∧ nextPos=Usize.wrapping_add pos 1#usize := by
  unfold Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body at ran
  split at ran
  all_goals
    repeat' first
    | (solve | cases ran)
    | uncase_result
    | head_reduce ran
    | split at ran
  all_goals cases Result.ok.inj ran;exact ⟨by assumption,rfl⟩

#print axioms advance
end AspisR1.Port9OR_BatchProgress
end
