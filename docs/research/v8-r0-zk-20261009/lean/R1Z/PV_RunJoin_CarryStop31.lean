import R1Z.PV_RunJoin_CarryFrame31
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CarryStop31
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open PV_RunJoin_CarryFrame31

theorem bit_value (index : U64) (level : Usize) (hl : level.val < 64) :
    (BuilderStdModels.shift64 index level &&& 1#u64).val =
      ((index.val >>> level.val) &&& 1) := by
  rw [UScalar.val_and,BuilderStdModels.shift64_spec]
  change ((index.bv.ushiftRight (level.val % 64)).toNat &&& 1) = _
  rw [Nat.mod_eq_of_lt hl]
  rfl
#print axioms bit_value

theorem stop [ExternalLinear] (index : U64) (roots : Roots)
    (frontier final : Frontier) (carry result : Digest) (level finish : Usize)
    (bound : level.val ≤ 20)
    (h : incremental_merkle.tree_reference.OwnedTree.append_one_loop
      index roots frontier carry level = ok (final,result,finish)) :
    finish.val = level.val + R0P.digestTrailingOnes (20-level.val) (index.val >>> level.val) := by
  generalize hn : 20-level.val = n
  induction n using Nat.strong_induction_on generalizing frontier carry level with
  | h n ih =>
    rw [incremental_merkle.tree_reference.OwnedTree.append_one_loop,format.POOL_V1_TREE_DEPTH] at h
    by_cases active : level < 20#usize
    · rw [if_pos active] at h
      simp only [lift,bind_tc_ok] at h
      have hl : level.val < 20 := active
      have hbval := bit_value index level (by omega)
      by_cases hb : BuilderStdModels.shift64 index level &&& 1#u64 = 1#u64
      · rw [if_pos hb] at h
        pv_peel h with sibling hs
        pv_peel h with parent hp
        rw [index_ok_gen roots level (by scalar_tac)] at h
        simp only [bind_tc_ok] at h
        rw [BuilderRecordsArray.update_gen frontier level _ (by simpa using hl)] at h
        simp only [bind_tc_ok] at h
        have hnext := BuilderRecordsArray.next_val level (by omega)
        have nextStop := ih (20-(Usize.wrapping_add level 1#usize).val) (by omega)
          _ parent _ (by omega) h rfl
        have hbit : ((index.val >>> level.val) &&& 1) ≠ 0 := by
          rw [hb] at hbval
          simp only [UScalar.ofNatCore_val_eq] at hbval
          omega
        rw [nextStop,hnext,← hn]
        rw [show 20-level.val = (20-(level.val+1))+1 by omega,
          R0P.digestTrailingOnes,if_neg hbit]
        rw [Nat.shiftRight_add]
        omega
      · rw [if_neg hb] at h
        have heq := congrArg (fun x : Frontier × Digest × Usize => x.2.2) (Result.ok.inj h)
        change level = finish at heq
        rw [← heq,← hn]
        have hbit : ((index.val >>> level.val) &&& 1) = 0 := by
          have hsmall : ((index.val >>> level.val) &&& 1) ≤ 1 := Nat.and_le_right
          have hne : ((index.val >>> level.val) &&& 1) ≠ 1 := by
            intro he
            apply hb
            apply UScalar.eq_of_val_eq
            simpa only [UScalar.ofNatCore_val_eq] using hbval.trans he
          omega
        rw [show 20-level.val = (20-(level.val+1))+1 by omega,
          R0P.digestTrailingOnes,if_pos hbit,Nat.add_zero]
    · rw [if_neg active] at h
      have heq := congrArg (fun x : Frontier × Digest × Usize => x.2.2) (Result.ok.inj h)
      change level = finish at heq
      rw [← heq,← hn]
      have he : level.val=20 := by change ¬level.val<20 at active; omega
      rw [he]
      rfl
#print axioms stop
end R1Z.PV_RunJoin_CarryStop31
