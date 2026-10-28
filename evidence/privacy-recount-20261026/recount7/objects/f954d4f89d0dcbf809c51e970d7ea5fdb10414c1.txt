import R1Z.PV_RunJoin_ZeroTree17
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ZeroValidation17
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open PV_RunJoin_ZeroTree17

/-- Completeness of the source frontier check when all twenty frontier cells
match the retained empty table. This is enough for the zero-index fixture. -/
theorem loop (index : U64) (frontier : Frontier) (empty : Roots)
    (same : ∀ j, j < 20 → frontier.val[j]! = empty.val[j]!)
    (level : Usize) (hl : level.val ≤ 20) :
    incremental_merkle.tree_reference.validate_owned_loop index frontier empty (.Ok ()) level = ok (.Ok ()) := by
  generalize he : 20-level.val = remaining
  induction remaining using Nat.strong_induction_on generalizing level with
  | h remaining ih =>
    rw [incremental_merkle.tree_reference.validate_owned_loop]
    simp only [format.POOL_V1_TREE_DEPTH]
    by_cases hlt : level.val < 20
    · rw [if_pos (by simpa [UScalar.lt_equiv] using hlt)]
      simp only [core.result.Result.is_ok,bind_tc_ok,lift,Bool.true_eq,if_true]
      have hn := BuilderRecordsArray.next_val level (by omega)
      split
      · rw [index_ok_gen frontier level (by simpa using hlt)]
        simp only [bind_tc_ok]
        rw [index_ok_gen empty level (by simp;omega)]
        simp only [bind_tc_ok]
        rw [same level.val hlt,PV_RunJoin_ZeroTree17.ne_self]
        simp only [bind_tc_ok,Bool.false_eq_true,if_false]
        exact ih (20-(Usize.wrapping_add level 1#usize).val) (by omega)
          (Usize.wrapping_add level 1#usize) (by omega) rfl
      · exact ih (20-(Usize.wrapping_add level 1#usize).val) (by omega)
          (Usize.wrapping_add level 1#usize) (by omega) rfl
    · rw [if_neg (by simpa [UScalar.lt_equiv] using hlt)]
#print axioms loop

theorem fixture : incremental_merkle.tree_reference.validate_owned_loop
    0#u64 PV_RunJoin_FixtureArguments.snapshot.frontier PV_Src_CanonicalRoots.table (.Ok ()) 0#usize = ok (.Ok ()) := by
  apply loop _ _ _ _ _ (by simp)
  intro j hj
  exact PV_RunJoin_ZeroTree17.frontier (UScalar.ofNatCore j (by scalar_tac)) (by simpa using hj)
#print axioms fixture
end R1Z.PV_RunJoin_ZeroValidation17
