/- Namespace port of BuilderBlockResult: same symbolic proof, actual forest extraction. -/
import R1Z.PV_Src_Forest_BlockArguments

/-! Complete actual block-writer call and totality. -/
set_option autoImplicit false
namespace R1Z.PV_Src_Forest_BlockResult
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_Src_Forest_DigestArguments PV_Src_Forest_DigestTotal PV_Src_Forest_TreeArguments PV_Src_Forest_BlockArguments
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder

theorem node_pre_total (right : Array U32 8#usize) : ∃ p, R0BlockCopies.node_pre right = ok p := by
  obtain ⟨pre,hp,_⟩ := node_pre_loop_spec right 8 0#usize (Array.repeat 16#usize 0#u32) (by simp)
  rw [R0BlockCopies.node_pre,hp]
  simp only [bind_tc_ok]
  rw [index_ok right 7#usize (by decide)]
  simp only [bind_tc_ok,R0BlockCopies.m31_add,lift]
  split <;> simp only [bind_tc_ok] <;> rw [update_ok pre 15#usize _ (by decide)] <;> exact ⟨_,rfl⟩

theorem writer_total (v : R0P.Variant) (R : RustChunks) (h : Nat) :
    ∃ b, RustWriterChain v R h = ok b := by
  unfold RustWriterChain
  split_ifs <;>
    repeat first
      | exact node_pre_total _
      | exact pre_total _ _
      | exact perm_total _ _
      | exact (by obtain ⟨b,hb,_⟩ := block_spec _ _ _;exact ⟨b,hb⟩)
      | exact (by obtain ⟨a,ha,_⟩ := node_absorb_spec _;exact ⟨a,ha⟩)
      | exact (by obtain ⟨a,ha,_⟩ := sponge_absorb_spec _ _;exact ⟨a,ha⟩)
      | apply bind_total
      | intro s

theorem writer (w : RW) (p : RP) (h : Usize) (hh : h.val < 57) :
    rust_writer_chain w p h = RustWriterChain (wordPublic p).variant
      (rustChunks (wordWitness w) (wordPublic p)) h.val := by
  rw [rust_writer_chain,PV_Src_Forest_BankShape.node_kind]
  simp only [bind_tc_ok,decide_eq_true_eq]
  change (if NodeKind h.val then _ else _) = _
  unfold RustWriterChain
  by_cases hn : NodeKind h.val
  · rw [if_pos hn,if_pos hn,children_eq w p h hh]
    simp only [bind_tc_ok,PV_Src_Forest_PrimitiveDigests.block_node_pre,PV_Src_Forest_PrimitiveDigests.block_node_absorb,
      perm_eq,PV_Src_Forest_PrimitiveDigests.block_write_block,rustChunks]
  · rw [if_neg hn,if_neg hn,PV_Src_Forest_BankShape.zero_kind]
    simp only [bind_tc_ok,decide_eq_true_eq]
    have hz : (p.transfer = false ∧ 27 ≤ h.val ∧ h.val ≤ 29) ↔
        ZeroKind (wordPublic p).variant h.val := by
      cases hp : p.transfer <;> simp [wordPublic,hp,ZeroKind]
    by_cases hzero : ZeroKind (wordPublic p).variant h.val
    · rw [if_pos (hz.mpr hzero),if_pos hzero]
      simp only [perm_eq,PV_Src_Forest_PrimitiveDigests.block_write_block,zero16]
    · rw [if_neg (show ¬(p.transfer = false ∧ 27 ≤ h.val ∧ h.val ≤ 29) from fun h => hzero (hz.mp h)),if_neg hzero]
      simp only [pre_state,chunk,chunk_len w p,bind_tc_ok,PV_Src_Forest_PrimitiveDigests.block_sponge_absorb,
        perm_eq,PV_Src_Forest_PrimitiveDigests.block_write_block]
      rfl

theorem writer_ok (w : RW) (p : RP) (h : Usize) (hh : h.val < 57) :
    rust_writer_chain w p h = ok (blockR (wordWitness w) (wordPublic p) h.val) := by
  obtain ⟨b,hb⟩ := writer_total (wordPublic p).variant (rustChunks (wordWitness w) (wordPublic p)) h.val
  rw [writer w p h hh,blockR,hb,okOr_ok]

#print axioms node_pre_total
#print axioms writer_total
#print axioms writer
#print axioms writer_ok
end R1Z.PV_Src_Forest_BlockResult
