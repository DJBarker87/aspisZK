import R1Z.PV_RunJoin_CarryMeaning31
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OwnedCarry31
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open PV_RunJoin_CarryFrame31
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
variable {K : Type} [Field K] [CharP K 2147483647]

theorem carry (pub : R0P.Public K) (leafMeaning : R0P.Digest K)
    (tree next : incremental_merkle.tree_reference.OwnedTree)
    (leaf : Digest) (receipt : incremental_merkle.AppendOneV1)
    (hi : tree.inner.next_leaf_index.val = pub.nextPairIndex)
    (hc : Canon8 leaf) (hm : digK leaf = leafMeaning)
    (hf : ∀ j : Fin 20, digK tree.inner.frontier.val[j.val]! = pub.snapshotFrontier j)
    (h : incremental_merkle.tree_reference.OwnedTree.append_one tree leaf = ok (.Ok (next,receipt)))
    (small : R0P.digestCarry pub.nextPairIndex < 20) :
    digK next.inner.frontier.val[R0P.digestCarry pub.nextPairIndex]! =
      AspisR1.AppendPath.pathPrefix pub leafMeaning (R0P.digestCarry pub.nextPairIndex) := by
  unfold incremental_merkle.tree_reference.OwnedTree.append_one at h
  pv_peel h with capacity hcapacity
  split at h
  · cases h
  · pv_peel h with carried hloop
    rcases carried with ⟨frontier,root,stop⟩
    have hstop := PV_RunJoin_CarryStop31.stop tree.inner.next_leaf_index tree.empty
      tree.inner.frontier frontier leaf root 0#usize stop (by decide) hloop
    have hstop' : stop.val = R0P.digestCarry pub.nextPairIndex := by
      simpa only [UScalar.ofNatCore_val_eq,Nat.sub_zero,Nat.shiftRight_zero,Nat.zero_add,hi,R0P.digestCarry] using hstop
    have hmean := PV_RunJoin_CarryMeaning31.meaning pub leafMeaning tree.inner.next_leaf_index hi
      tree.empty tree.inner.frontier frontier leaf root 0#usize stop (by decide) hc hm
      (fun j _ => hf j) hloop
    simp only [lift,bind_tc_ok] at h
    split at h
    · rename_i full
      have hv : stop.val=20 := by
        simpa only [format.POOL_V1_TREE_DEPTH,UScalar.ofNatCore_val_eq] using congrArg UScalar.val full
      omega
    · have hs : stop.val<20 := by omega
      rw [BuilderRecordsArray.update_gen frontier stop root (by simpa using hs)] at h
      simp only [bind_tc_ok] at h
      have hread : digK (frontier.set stop root).val[R0P.digestCarry pub.nextPairIndex]! =
          AspisR1.AppendPath.pathPrefix pub leafMeaning (R0P.digestCarry pub.nextPairIndex) := by
        rw [BuilderRecordsArray.set_get _ _ _ _ (by simpa using hs),if_pos (by omega),← hstop']
        exact hmean.2
      repeat' first
        | (pv_peel h with value hvalue)
        | exact False.elim (PV_Src_ResultControl.error_ne_ok _ _ h)
        | exact False.elim (PV_Src_ResultControl.same_residual_ne_ok _ _ h)
        | (have _test : core.ops.control_flow.ControlFlow _ _ := value; cases value)
        | (cases h; exact hread)
#print axioms carry
end R1Z.PV_RunJoin_OwnedCarry31
