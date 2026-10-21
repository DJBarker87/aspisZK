import R1Z.BuilderForestValidatorSteps
import R1Z.BuilderRecordsFields

/-! Exact successful-frontier admission at the projected validator boundary.
No root validity, semantic spend relation, or source RuntimeJoin is assumed. -/
set_option autoImplicit false
namespace R1Z.BuilderForestValidatorAcceptance
open Aeneas Aeneas.Std Result AspisBuilderForestValidator
open pool_v1.incremental_merkle BuilderForestValidatorSteps BuilderRecordsFields

inductive Accepted (index : U64) (a : Frontier) (empty : Roots) : Nat → Usize → Prop
  | done (level : Usize) : Accepted index a empty 0 level
  | step (n : Nat) (level : Usize)
      (head : checkStep index a empty level = ok (.Ok ()))
      (tail : Accepted index a empty n (Usize.wrapping_add level 1#usize)) :
      Accepted index a empty (n+1) level

theorem early_accepts (index : U64) (a : Frontier) (empty : Roots)
    (n : Nat) (level : Usize) :
    early index a empty n level = ok (.Ok ()) ↔ Accepted index a empty n level := by
  induction n generalizing level with
  | zero => exact ⟨fun _ => .done level, fun _ => rfl⟩
  | succ n ih =>
    constructor
    · intro h
      rw [early] at h
      cases hs : checkStep index a empty level with
      | ok r => cases r with
        | Ok u => cases u; exact .step n level hs ((ih _).mp (by simpa [hs] using h))
        | Err e => simp [hs] at h
      | fail e => simp [hs] at h
      | div => simp [hs] at h
    · intro h
      cases h with
      | step n level head tail => rw [early,head]; exact (ih _).mpr tail

theorem loop_accepts (index : U64) (a : Frontier) (empty : Roots) :
    tree_reference.validate_owned_loop index a empty (.Ok ()) 0#usize = ok (.Ok ()) ↔
      Accepted index a empty 20 0#usize := by
  rw [complete_frontier]
  exact early_accepts index a empty 20 0#usize

/-- Acceptance demands each actual projected array comparison succeeds;
this statement cannot be supplied merely by an arbitrary boolean scan. -/
theorem first_check (index : U64) (a : Frontier) (empty : Roots)
    (h : tree_reference.validate_owned_loop index a empty (.Ok ()) 0#usize = ok (.Ok ())) :
    checkStep index a empty 0#usize = ok (.Ok ()) := by
  have accepted := (loop_accepts index a empty).mp h
  cases accepted with
  | step _ _ head _ => exact head

/-- Success of the entire projected validator, for any root helper,
forces every one of the twenty frontier checks, not just the first check. -/
theorem validator_success
    (reconstruct : IncrementalMerkleTreeV1 → Roots →
      Result (core.result.Result Digest PoolV1TreeError))
    (tree : IncrementalMerkleTreeV1) (empty : Roots)
    (h : tree_reference.validate_owned reconstruct tree empty = ok (.Ok ())) :
    Accepted tree.next_leaf_index tree.frontier empty 20 0#usize := by
  have capacity : POOL_V1_LEAF_CAPACITY = ok 1048576#u64 := rfl
  rw [tree_reference.validate_owned,capacity] at h
  simp only [bind_tc_ok] at h
  split at h
  · cases h
  · obtain ⟨verdict,hv,hr⟩ := bind_ok_inv h
    cases verdict with
    | Ok u => cases u; exact (loop_accepts _ _ _).mp hv
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame] at hr

#print axioms early_accepts
#print axioms loop_accepts
#print axioms first_check
#print axioms validator_success
end R1Z.BuilderForestValidatorAcceptance
