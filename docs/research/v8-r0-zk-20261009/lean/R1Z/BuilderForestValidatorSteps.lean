import R1Z.BuilderForestValidatorExtracted
import R1Z.BuilderRecordsArray

/-! Symbolic induction replaces the timed-out whole-validator comparison.
The step retains array/index/comparison failures; the root helper is unchanged
and projected as an explicit function in the extracted wrapper. -/
set_option autoImplicit false
namespace R1Z.BuilderForestValidatorSteps
open Aeneas Aeneas.Std Result AspisBuilderForestValidator
open pool_v1.incremental_merkle
abbrev Digest := Array U32 8#usize
abbrev Frontier := Array Digest 20#usize
abbrev Roots := Array Digest 21#usize
abbrev Verdict := core.result.Result Unit PoolV1TreeError

def checkStep (index : U64) (a : Frontier) (empty : Roots) (level : Usize) : Result Verdict := do
  let bit := BuilderStdModels.shift64 index level &&& 1#u64
  if bit = 0#u64 then
    let node ← Array.index_usize a level
    let zero ← Array.index_usize empty level
    let mismatch ← core.array.equality.PartialEqArray.ne
      aspis_core.field.M31.Insts.CoreCmpPartialEqM31 node zero
    if mismatch then ok (.Err .NonCanonicalFrontier) else ok (.Ok ())
  else ok (.Ok ())

def early (index : U64) (a : Frontier) (empty : Roots) : Nat → Usize → Result Verdict
  | 0, _ => ok (.Ok ())
  | n+1, level => do
    let r ← checkStep index a empty level
    match r with
    | .Err e => ok (.Err e)
    | .Ok _ => early index a empty n (Usize.wrapping_add level 1#usize)

theorem loop_error (index : U64) (a : Frontier) (empty : Roots)
    (level : Usize) (e : PoolV1TreeError) :
    tree_reference.validate_owned_loop index a empty (.Err e) level = ok (.Err e) := by
  rw [tree_reference.validate_owned_loop]
  split <;> rfl

theorem loop_stop (index : U64) (a : Frontier) (empty : Roots)
    (level : Usize) (h : level.val = 20) :
    tree_reference.validate_owned_loop index a empty (.Ok ()) level = ok (.Ok ()) := by
  rw [tree_reference.validate_owned_loop]
  rw [if_neg (by simpa [pool_v1.format.POOL_V1_TREE_DEPTH,UScalar.lt_equiv] using (show ¬level.val < 20 by omega))]

theorem loop_step (index : U64) (a : Frontier) (empty : Roots)
    (level : Usize) (h : level.val < 20) :
    tree_reference.validate_owned_loop index a empty (.Ok ()) level = (do
      let r ← checkStep index a empty level
      tree_reference.validate_owned_loop index a empty r (Usize.wrapping_add level 1#usize)) := by
  rw [tree_reference.validate_owned_loop]
  rw [if_pos (by simpa [pool_v1.format.POOL_V1_TREE_DEPTH,UScalar.lt_equiv] using h)]
  simp only [core.result.Result.is_ok,bind_tc_ok,lift,↓reduceIte]
  simp only [checkStep]
  by_cases hb : BuilderStdModels.shift64 index level &&& 1#u64 = 0#u64
  · rw [if_pos hb,if_pos hb]
    simp only [bind_assoc]
    congr 1
    funext node
    congr 1
    funext zero
    congr 1
    funext mismatch
    cases mismatch <;> rfl
  · rw [if_neg hb,if_neg hb]; rfl

/-- No fixed twenty-step solver unwinding: n is symbolic. -/
theorem loop_early (index : U64) (a : Frontier) (empty : Roots)
    (n : Nat) (level : Usize) (h : level.val+n=20) :
    tree_reference.validate_owned_loop index a empty (.Ok ()) level = early index a empty n level := by
  induction n generalizing level with
  | zero => exact loop_stop index a empty level (by omega)
  | succ n ih =>
    rw [loop_step index a empty level (by omega),early]
    have hn := BuilderRecordsArray.next_val level (by omega)
    have ht := ih (Usize.wrapping_add level 1#usize) (by omega)
    cases hs : checkStep index a empty level with
    | ok r => cases r with
      | Ok u => cases u; simpa only [hs,bind_tc_ok] using ht
      | Err e => simp only [hs,bind_tc_ok]; exact loop_error index a empty _ e
    | fail e => rfl
    | div => rfl

theorem complete_frontier (index : U64) (a : Frontier) (empty : Roots) :
    tree_reference.validate_owned_loop index a empty (.Ok ()) 0#usize =
      early index a empty 20 0#usize :=
  loop_early index a empty 20 0#usize (by simp)

#print axioms loop_error
#print axioms loop_stop
#print axioms loop_step
#print axioms loop_early
#print axioms complete_frontier
end R1Z.BuilderForestValidatorSteps
