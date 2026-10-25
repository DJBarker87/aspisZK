import Port12COUNT_Verify
import Port9OR_Batch
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port12COUNT_BatchLeaf
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2 CheckpointBytes5Effect
open Port9OR_BatchStep (Indices Values Next Out)
open Port12COUNT_Verify
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem lift_cap {A B Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (hash : Hash) (H : Bytes → State) (r : Result A) (k : A → Code B) (n : Nat)
    (tail : ∀ a, (eval H (Port9OR_Code.program D hash (k a))).1.length≤n) :
    (eval H (Port9OR_Code.program D hash (liftResult r >>= k))).1.length≤n := by
  rw [eval_lift_join]
  cases r with
  | ok a => exact tail a
  | fail e => exact Nat.zero_le n
  | div => exact Nat.zero_le n

/-- Includes the duplicate leaf read BEFORE the duplicate comparison. -/
theorem active (base : Port3_NativeBatchBody.Ops) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (H : Bytes → State)
    (proof : Slice U8) (root : Digest) (tree lo n slot : Usize) (keys : Array U64 16#usize)
    (idx : Indices) (val : Values) (d pos : Usize) (running : pos<n) :
    (eval H (Port9OR_Code.program D hash
      (Port9OR_BatchStep.body base D proof root tree hash lo n slot keys idx val d pos))).1.length≤1 := by
  unfold Port9OR_BatchStep.body
  rw [if_pos running]
  repeat' first
  | (apply lift_cap; intro x)
  | (apply bind_count D hash H _ _ 1 0 (Port11PROV_SourceCount.leaf_count D hash H _ _); intro leaf _)
  | (solve | exact Nat.zero_le 0)
  | split
  all_goals rfl

/-- Exact source continuation shape; no assumption on sortedness or digest. -/
theorem cont_shape (base : Port3_NativeBatchBody.Ops) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (proof : Slice U8) (root : Digest) (tree lo n slot : Usize) (keys : Array U64 16#usize)
    (idx : Indices) (val : Values) (d pos : Usize)
    (nextIdx : Indices) (nextVal : Values) (nextD nextPos : Usize)
    (ran : Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port9OR_BatchStep.ops base) D proof root tree hash lo n slot keys idx val d pos=
        ok (.cont (nextIdx,nextVal,nextD,nextPos))) :
    nextD=d ∨ nextD=Usize.wrapping_add d 1#usize := by
  unfold Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body at ran
  split at ran
  all_goals
    repeat' first
    | (solve | cases ran)
    | uncase_result
    | head_reduce ran
    | split at ran
  all_goals cases Result.ok.inj ran; first | exact Or.inl rfl | exact Or.inr rfl

#print axioms lift_cap
#print axioms active
#print axioms cont_shape
end AspisR1.Port12COUNT_BatchLeaf
end
