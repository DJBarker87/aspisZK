import R1Z.PV_RunJoin_UniversalTreeFrame22
import R1Z.BuilderRecordsArray
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CarryFrame31
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
abbrev Digest := Array U32 8#usize
abbrev Frontier := Array Digest 20#usize
abbrev Roots := Array Digest 21#usize

/-- A symbolic frame for the carry loop.
Only cells strictly below the returned level can have been cleared. -/
theorem frame [ExternalLinear] (index : U64) (roots : Roots)
    (frontier final : Frontier) (carry result : Digest) (level stop : Usize)
    (bound : level.val ≤ 20)
    (h : incremental_merkle.tree_reference.OwnedTree.append_one_loop
      index roots frontier carry level = ok (final,result,stop)) :
    level.val ≤ stop.val ∧ stop.val ≤ 20 ∧
      ∀ j : Fin 20, stop.val ≤ j.val → final.val[j.val]! = frontier.val[j.val]! := by
  generalize hn : 20-level.val = n
  induction n using Nat.strong_induction_on generalizing frontier carry level with
  | h n ih =>
    rw [incremental_merkle.tree_reference.OwnedTree.append_one_loop,
      format.POOL_V1_TREE_DEPTH] at h
    by_cases active : level < 20#usize
    · rw [if_pos active] at h
      simp only [lift,bind_tc_ok] at h
      split at h
      · pv_peel h with sibling hs
        pv_peel h with parent hp
        rw [index_ok_gen roots level (by scalar_tac)] at h
        simp only [bind_tc_ok] at h
        have hl : level.val < 20 := by simpa only [UScalar.lt_equiv,UScalar.ofNatCore_val_eq] using active
        rw [BuilderRecordsArray.update_gen frontier level _ (by simpa using hl)] at h
        simp only [bind_tc_ok] at h
        have hnxt := BuilderRecordsArray.next_val level (by omega)
        have nextFrame := ih (20-(Usize.wrapping_add level 1#usize).val) (by omega)
          _ parent _ (by omega) h rfl
        refine ⟨by omega,nextFrame.2.1,?_⟩
        intro j hj
        rw [nextFrame.2.2 j hj,BuilderRecordsArray.set_get _ _ _ _ (by simpa using hl),if_neg (by omega)]
      · obtain ⟨rfl,rfl,rfl⟩ := Prod.mk.inj (Result.ok.inj h)
        exact ⟨le_rfl,bound,fun _ _ => rfl⟩
    · rw [if_neg active] at h
      obtain ⟨rfl,rfl,rfl⟩ := Prod.mk.inj (Result.ok.inj h)
      exact ⟨le_rfl,bound,fun _ _ => rfl⟩
#print axioms frame
end R1Z.PV_RunJoin_CarryFrame31
