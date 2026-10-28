import R1Z.PV_RunJoin_CarryStop31
import R1Z.PV_RunJoin_LaneField31
import R1AppendPath
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CarryMeaning31
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open PV_RunJoin_CarryFrame31
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
variable {K : Type} [Field K] [CharP K 2147483647]
attribute [local irreducible] R0P.nodeCompress R0P.poseidonPermutation

theorem meaning (pub : R0P.Public K) (leaf : R0P.Digest K)
    (index : U64) (hi : index.val = pub.nextPairIndex) (roots : Roots)
    (frontier final : Frontier) (carry result : Digest) (level finish : Usize)
    (bound : level.val ≤ 20) (hc : Canon8 carry)
    (hm : digK carry = AspisR1.AppendPath.pathPrefix pub leaf level.val)
    (hf : ∀ j : Fin 20, level.val ≤ j.val → digK frontier.val[j.val]! = pub.snapshotFrontier j)
    (h : incremental_merkle.tree_reference.OwnedTree.append_one_loop
      index roots frontier carry level = ok (final,result,finish)) :
    Canon8 result ∧ digK result = AspisR1.AppendPath.pathPrefix pub leaf finish.val := by
  generalize hn : 20-level.val = n
  induction n using Nat.strong_induction_on generalizing frontier carry level with
  | h n ih =>
    rw [incremental_merkle.tree_reference.OwnedTree.append_one_loop,format.POOL_V1_TREE_DEPTH] at h
    by_cases active : level < 20#usize
    · rw [if_pos active] at h
      simp only [lift,bind_tc_ok] at h
      have hl : level.val < 20 := active
      by_cases hb : BuilderStdModels.shift64 index level &&& 1#u64 = 1#u64
      · rw [if_pos hb,index_ok_gen frontier level (by simpa using hl)] at h
        simp only [bind_tc_ok] at h
        pv_peel h with parent hp
        rw [index_ok_gen roots level (by scalar_tac)] at h
        simp only [bind_tc_ok] at h
        rw [BuilderRecordsArray.update_gen frontier level _ (by simpa using hl)] at h
        simp only [bind_tc_ok] at h
        obtain ⟨actual,ha,hcanon,hmeaning⟩ := PV_RunJoin_LaneField31.parent_source (K := K) frontier.val[level.val]! carry hc
        rw [hp] at ha
        cases Result.ok.inj ha
        have hnext := BuilderRecordsArray.next_val level (by omega)
        have hbit : ¬R0P.digestBitZero pub ⟨level.val,hl⟩ := by
          have hv := PV_RunJoin_CarryStop31.bit_value index level (by omega)
          rw [hb,hi] at hv
          simp only [UScalar.ofNatCore_val_eq] at hv
          change ¬((pub.nextPairIndex >>> level.val) &&& 1)=0
          omega
        have hmnext : digK parent = AspisR1.AppendPath.pathPrefix pub leaf (Usize.wrapping_add level 1#usize).val := by
          rw [hnext,AspisR1.AppendPath.pathPrefix,dif_pos hl,AspisR1.AppendPath.step,if_neg hbit]
          rw [hmeaning,hm,hf ⟨level.val,hl⟩ (le_refl _)]
        apply ih (20-(Usize.wrapping_add level 1#usize).val) (by omega)
          _ parent _ (by omega) hcanon hmnext _ h rfl
        intro j hj
        rw [BuilderRecordsArray.set_get _ _ _ _ (by simpa using hl),if_neg (by omega)]
        exact hf j (by omega)
      · rw [if_neg hb] at h
        obtain ⟨rfl,rfl,rfl⟩ := Prod.mk.inj (Result.ok.inj h)
        exact ⟨hc,hm⟩
    · rw [if_neg active] at h
      obtain ⟨rfl,rfl,rfl⟩ := Prod.mk.inj (Result.ok.inj h)
      exact ⟨hc,hm⟩
#print axioms meaning
end R1Z.PV_RunJoin_CarryMeaning31
