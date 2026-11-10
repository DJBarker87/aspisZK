import NPH_R22QRawShift
import AspisR1TerminalDecoder.Funs

/-! NPH_ (R22 item 4): a guarded usize increment never overflows, and the two
digest_is_canonical loop bodies of AspisR1TerminalDecoder are checked-total for every input
(their only checked arithmetic is the guarded `i + 1`). Standard axioms; no merged module
is changed. -/
set_option autoImplicit false
namespace AspisR1.NPH_R22Loops
open Aeneas Aeneas.Std Result AspisR1.NPH_R22FieldRef

/-- Generic: a guarded usize increment `x + 1` (x < n for a machine n) succeeds. -/
theorem usize_succ_ok (x n : Usize) (h : x.val < n.val) :
    ∃ z, (x + 1#usize : Result Usize) = ok z ∧ z.val = x.val + 1 := by
  have hn : n.val < 2 ^ UScalarTy.numBits .Usize := n.bv.isLt
  apply add_ok
  have h1 : (1#usize : Usize).val = 1 := by first | rfl | simp | decide
  rw [h1]; simp only [UScalar.max]; omega

/-- TOTAL: AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.digest_is_canonical_loop.body, every input. -/
theorem pair_forest_accounts_digest_is_canonical_body_total (a : Array aspis_core.field.M31 8#usize) (i : Usize) :
    ∃ v, AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.digest_is_canonical_loop.body a i = ok v := by
  unfold AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.digest_is_canonical_loop.body
  simp only [lift, bind_tc_ok]
  by_cases hi : i < Slice.len (Array.to_slice a)
  · have hlen : i.val < a.length := by
      have := hi; first | (simp only [Slice.len, Array.to_slice] at this; exact this) | (simpa using this) | exact this
    obtain ⟨m, hm, _⟩ := WP.spec_imp_exists (Array.index_usize_spec a i hlen)
    obtain ⟨z, hz, _⟩ := usize_succ_ok i (Slice.len (Array.to_slice a)) hi
    simp only [hi, ↓reduceIte, hm, bind_tc_ok]
    split
    · exact ⟨_, rfl⟩
    · simp only [hz, bind_tc_ok]; exact ⟨_, rfl⟩
  · simp only [hi, ↓reduceIte]; exact ⟨_, rfl⟩

/-- TOTAL: AspisR1TerminalDecoder.pool_v1.pair_tree_profile.digest_is_canonical_loop.body, every input. -/
theorem pair_tree_profile_digest_is_canonical_body_total (a : Array aspis_core.field.M31 8#usize) (i : Usize) :
    ∃ v, AspisR1TerminalDecoder.pool_v1.pair_tree_profile.digest_is_canonical_loop.body a i = ok v := by
  unfold AspisR1TerminalDecoder.pool_v1.pair_tree_profile.digest_is_canonical_loop.body
  simp only [lift, bind_tc_ok]
  by_cases hi : i < Slice.len (Array.to_slice a)
  · have hlen : i.val < a.length := by
      have := hi; first | (simp only [Slice.len, Array.to_slice] at this; exact this) | (simpa using this) | exact this
    obtain ⟨m, hm, _⟩ := WP.spec_imp_exists (Array.index_usize_spec a i hlen)
    obtain ⟨z, hz, _⟩ := usize_succ_ok i (Slice.len (Array.to_slice a)) hi
    simp only [hi, ↓reduceIte, hm, bind_tc_ok]
    split
    · exact ⟨_, rfl⟩
    · simp only [hz, bind_tc_ok]; exact ⟨_, rfl⟩
  · simp only [hi, ↓reduceIte]; exact ⟨_, rfl⟩

#print axioms usize_succ_ok
#print axioms pair_forest_accounts_digest_is_canonical_body_total
#print axioms pair_tree_profile_digest_is_canonical_body_total
end AspisR1.NPH_R22Loops
