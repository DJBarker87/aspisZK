import R1Z.BuilderAppendArguments
import R1Z.BuilderBankShape

/-! Actual node and sponge arguments for the 57 copy blocks. -/
set_option autoImplicit false
namespace R1Z.BuilderBlockArguments
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderPrimitiveArguments BuilderDigestArguments BuilderAuxContent BuilderTreeArguments
  BuilderDigestTotal BuilderAppendArguments
open AspisBuilderGlueSource.pool_v1.pair_forest_copy_builder

theorem membership (w : RW) (p : RP) (n : Usize) (hn : n.val < 24) :
    (do let c ← tree_cur_r w p n
        let s ← Array.index_usize w.sibs n
        let b ← bit_b w n
        ordered_r c s b) =
    ok (orderedR (okOr (treeCurR (wordWitness w) (wordPublic p) n.val) zero8)
      w.sibs.val[n.val]! (bitB (wordWitness w) n.val)) := by
  rw [tree_ok w p n (by omega)]
  simp only [bind_tc_ok]
  rw [index_ok_gen _ n (by simpa using hn)]
  simp only [bind_tc_ok]
  rw [bit w n hn]
  simp only [bind_tc_ok,ordered]

theorem append_children (w : RW) (p : RP) (n : Usize) (hn : n.val < 20) :
    (do let c ← app_cur_r w p n
        let s ← app_sib_r p n
        let b ← app_bit_r p n
        ordered_r c s b) =
    ok (orderedR (okOr (appCurR (wordWitness w) (wordPublic p) n.val) zero8)
      (appSibR (wordPublic p) n.val) (appBitR (wordPublic p) n.val)) := by
  rw [append_ok w p n (by omega)]
  simp only [bind_tc_ok]
  rw [append_sibling p n hn]
  simp only [bind_tc_ok]
  rw [append_bit p n (by omega)]
  simp only [bind_tc_ok,ordered]

theorem change_ok (w : RW) (p : RP) :
    change_dr w p = ok (okOr (changeDR (wordWitness w) (wordPublic p)) zero8) := by
  obtain ⟨d,hd⟩ := note_total (chunksOf (wordWitness w) (wordPublic p)) 32
  rw [change_digest,show changeDR (wordWitness w) (wordPublic p) = ok d from hd,okOr_ok]

theorem recipient_ok (w : RW) (p : RP) :
    recip_dr w p = ok (okOr (recipDR (wordWitness w) (wordPublic p)) zero8) := by
  obtain ⟨d,hd⟩ := note_total (chunksOf (wordWitness w) (wordPublic p)) 29
  rw [recipient_digest,show recipDR (wordWitness w) (wordPublic p) = ok d from hd,okOr_ok]

attribute [local irreducible] treeCurR appCurR orderedR changeDR recipDR bitB appBitR appSibR

theorem children_eq (w : RW) (p : RP) (h : Usize) (hh : h.val < 57) :
    children w p h = ok (childrenOf (wordWitness w) (wordPublic p) h.val) := by
  simp only [children,childrenOf,UScalar.le_equiv,scalar_eq,UScalar.ofNatCore_val_eq,
    lift,bind_tc_ok,wordPublic]
  split_ifs <;> try omega
  all_goals
    first
    | have hn : (Usize.wrapping_sub h 4#usize).val < 24 := by
        rw [R0Z.WriterRefine.usub _ _ (by simp;omega)];simp;omega
      have hv : (Usize.wrapping_sub h 4#usize).val = h.val-4 := by
        rw [R0Z.WriterRefine.usub _ _ (by simp;omega)];rfl
      rw [membership w p (Usize.wrapping_sub h 4#usize) hn,hv]
    | have hn : (Usize.wrapping_sub h 33#usize).val < 24 := by
        rw [R0Z.WriterRefine.usub _ _ (by simp;omega)];simp;omega
      have hv : (Usize.wrapping_sub h 33#usize).val = h.val-33 := by
        rw [R0Z.WriterRefine.usub _ _ (by simp;omega)];rfl
      rw [membership w p (Usize.wrapping_sub h 33#usize) hn,hv]
    | have hn : (Usize.wrapping_sub h 34#usize).val < 20 := by
        rw [R0Z.WriterRefine.usub _ _ (by simp;omega)];simp;omega
      have hv : (Usize.wrapping_sub h 34#usize).val = h.val-34 := by
        rw [R0Z.WriterRefine.usub _ _ (by simp;omega)];rfl
      rw [append_children w p (Usize.wrapping_sub h 34#usize) hn,hv]
    | skip
  all_goals try simp only [change_ok,recipient_ok,bind_tc_ok,zero_digest]
  all_goals try simp (disch := omega) only [R0Z.WriterRefine.usub,UScalar.ofNatCore_val_eq]
  all_goals try simp_all only [wordPublic,if_true,if_false,Bool.false_eq_true]
  all_goals rfl

#print axioms membership
#print axioms append_children
#print axioms change_ok
#print axioms recipient_ok
#print axioms children_eq
end R1Z.BuilderBlockArguments
