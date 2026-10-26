/- Namespace port of BuilderTreeArguments: same symbolic proof, actual forest extraction. -/
import R1Z.PV_Src_Forest_AuxContent

/-! Membership digest arguments and totality. The induction variable is
symbolic; no concrete Merkle path is evaluated. -/
set_option autoImplicit false
namespace R1Z.PV_Src_Forest_TreeArguments
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_Src_Forest_DigestArguments PV_Src_Forest_AuxContent PV_Src_Forest_DigestTotal
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder

theorem node_total (left right : Array U32 8#usize) : ∃ d, nodeDigestR left right = ok d := by
  obtain ⟨pre,hp,_⟩ := node_pre_loop_spec right 8 0#usize (Array.repeat 16#usize 0#u32) (by simp)
  have hp' : ∃ p, R0BlockCopies.node_pre right = ok p := by
    rw [R0BlockCopies.node_pre,hp]
    simp only [bind_tc_ok]
    rw [index_ok right 7#usize (by decide)]
    simp only [bind_tc_ok,R0BlockCopies.m31_add,lift]
    split <;> simp only [bind_tc_ok] <;> rw [update_ok pre 15#usize _ (by decide)] <;> exact ⟨_,rfl⟩
  obtain ⟨pre,hp⟩ := hp'
  obtain ⟨ab,ha,_⟩ := node_absorb_spec left
  obtain ⟨d,hd⟩ := block_total pre ab
  exact ⟨d,by rw [nodeDigestR,hp];simp only [bind_tc_ok];rw [ha];simp only [bind_tc_ok];exact hd⟩

theorem tree_total (W : RustWitness) (P : RustPublic) (n : Nat) :
    ∃ c, treeCurR W P n = ok c := by
  induction n with
  | zero => exact note_total (chunksOf W P) 3
  | succ n ih =>
    obtain ⟨c,hc⟩ := ih
    obtain ⟨d,hd⟩ := node_total (orderedR c W.sibs.val[n]! (bitB W n)).1
      (orderedR c W.sibs.val[n]! (bitB W n)).2
    exact ⟨d,by rw [treeCurR,hc];simp only [bind_tc_ok];exact hd⟩

theorem bit (w : RW) (l : Usize) (hl : l.val < 24) :
    bit_b w l = ok (bitB (wordWitness w) l.val) := by
  rw [bit_b,index_ok w.bits l (by simpa using hl)]
  simp only [bind_tc_ok,bitB,wordWitness]
  let x := w.bits.val[l.val]!
  change ok (x != 0#u32) = ok (decide (x.val ≠ 0))
  by_cases hx : x = 0#u32
  · rw [hx];rfl
  · have hv : x.val ≠ 0 := by intro h;apply hx;apply UScalar.eq_of_val_eq;simpa using h
    simp [hx,hv]

theorem ordered (cur sib : Array U32 8#usize) (b : Bool) :
    ordered_r cur sib b = ok (orderedR cur sib b) := by
  cases b <;> rfl

theorem tree (w : RW) (p : RP) (n : Usize) (hn : n.val ≤ 24) :
    tree_cur_r w p n = treeCurR (wordWitness w) (wordPublic p) n.val := by
  generalize he : n.val = k
  induction k using Nat.strong_induction_on generalizing n with
  | h k ih =>
    rw [tree_cur_r]
    by_cases hz : n.val = 0
    · have hn0 : n = 0#usize := by apply UScalar.eq_of_val_eq;simpa using hz
      rw [if_pos hn0,← he,hz]
      exact input_digest w p
    · have hn0 : n ≠ 0#usize := by intro h;apply hz;simpa [h] using congrArg UScalar.val h
      rw [if_neg hn0]
      simp only [lift,bind_tc_ok]
      have hv : (Usize.wrapping_sub n 1#usize).val = n.val-1 :=
        R0Z.WriterRefine.usub _ _ (by simp;omega)
      have hk : (Usize.wrapping_sub n 1#usize).val < k := by omega
      rw [ih _ hk _ (by omega) rfl]
      rw [index_ok_gen w.sibs _ (by rw [hv];simp;omega)]
      simp only [bind_tc_ok]
      rw [bit w _ (by rw [hv];omega)]
      simp only [bind_tc_ok,ordered,node_digest]
      rw [hv]
      conv_rhs => rw [← he,show n.val = (n.val-1)+1 by omega,treeCurR]
      rfl

theorem tree_ok (w : RW) (p : RP) (n : Usize) (hn : n.val ≤ 24) :
    tree_cur_r w p n = ok (okOr (treeCurR (wordWitness w) (wordPublic p) n.val) zero8) := by
  obtain ⟨c,hc⟩ := tree_total (wordWitness w) (wordPublic p) n.val
  rw [tree w p n hn,hc,okOr_ok]

#print axioms node_total
#print axioms tree_total
#print axioms bit
#print axioms ordered
#print axioms tree
#print axioms tree_ok
end R1Z.PV_Src_Forest_TreeArguments
