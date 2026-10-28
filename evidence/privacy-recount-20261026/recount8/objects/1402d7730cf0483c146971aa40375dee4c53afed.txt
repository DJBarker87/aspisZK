import R0Z.ReadBackRefine

/-! The extracted sponge writer (copy of write_sponge, pair_trace.rs:304-354;
DESIGN-BUILDER-MODEL §10), with the permutation abstract.  `sponge_model`:
given model blocks B 0..perms-1 whose first pre-state is the sponge's initial
state, whose next pre-state is the previous block's output (the sponge
chaining of the model's noteB1/noteB2/nulB1), whose absorptions are the
chunks, and whose rounds satisfy RoundsOk, the written blocks lift to
`blockCell (B p)` cell by cell. -/
set_option autoImplicit false

namespace R0Z.WriterRefine
open Aeneas Aeneas.Std Result

theorem sponge_init_spec (domain len : U32) :
    ∃ s, R0BlockCopies.sponge_init domain len = ok s ∧
      ∀ k, s.val[k]! = if k = 8 then domain else if k = 9 then len else 0#u32 := by
  have h8 : (8#usize : Usize).val < (16#usize).val := by simp
  have h9 : (9#usize : Usize).val < (16#usize).val := by simp
  refine ⟨((Array.repeat 16#usize 0#u32).set 8#usize domain).set 9#usize len, ?_, fun k => ?_⟩
  · rw [R0BlockCopies.sponge_init, update_ok _ _ _ h8]
    simp only [bind_tc_ok]
    rw [update_ok _ _ _ h9]
  · rw [set_get' _ _ _ h9 k, set_get' _ _ _ h8 k, rep16, show (8#usize : Usize).val = 8 by simp,
      show (9#usize : Usize).val = 9 by simp]
    split_ifs <;> first | rfl | omega

theorem sponge_absorb_loop_spec (chunk : Array U32 8#usize) (len : Usize) :
    ∀ (n : Nat) (lane : Usize) (ab : Array U32 16#usize), lane.val + n = 8 →
      ∃ a', R0BlockCopies.sponge_absorb_loop chunk len ab lane = ok a' ∧
        ∀ k, a'.val[k]! = if lane.val ≤ k ∧ k < 8 ∧ k < len.val then chunk.val[k]! else ab.val[k]!
  | 0, lane, ab, h => by
      refine ⟨ab, ?_, fun k => by rw [if_neg (by omega)]⟩
      rw [R0BlockCopies.sponge_absorb_loop, if_neg (by rw [UScalar.lt_equiv]; scalar_tac)]
  | n + 1, lane, ab, h => by
      have hlt : lane < 8#usize := by rw [UScalar.lt_equiv]; scalar_tac
      have hb : lane.val < (8#usize).val := by simp; omega
      have hb16 : lane.val < (16#usize).val := by simp; omega
      have hl1 : (Usize.wrapping_add lane 1#usize).val = lane.val + 1 := uadd _ _ (by scalar_tac)
      by_cases hl : lane < len
      · have hl' : lane.val < len.val := by rw [UScalar.lt_equiv] at hl; exact hl
        obtain ⟨a', ha', hs⟩ := sponge_absorb_loop_spec chunk len n (Usize.wrapping_add lane 1#usize)
          (ab.set lane (chunk.val[lane.val]!)) (by rw [hl1]; omega)
        refine ⟨a', ?_, fun k => ?_⟩
        · rw [R0BlockCopies.sponge_absorb_loop, if_pos hlt, if_pos hl, index_ok chunk lane hb]
          simp only [bind_tc_ok]
          rw [update_ok ab lane _ hb16]
          simp only [bind_tc_ok, lift]
          exact ha'
        · rw [hs k, hl1, set_get' ab lane _ hb16 k]
          split_ifs <;> first | rfl | omega | (subst_vars; rfl)
      · have hl' : ¬ lane.val < len.val := by rw [UScalar.lt_equiv] at hl; exact hl
        obtain ⟨a', ha', hs⟩ := sponge_absorb_loop_spec chunk len n (Usize.wrapping_add lane 1#usize)
          ab (by rw [hl1]; omega)
        refine ⟨a', ?_, fun k => ?_⟩
        · rw [R0BlockCopies.sponge_absorb_loop, if_pos hlt, if_neg hl]
          simp only [bind_tc_ok, lift]
          exact ha'
        · rw [hs k, hl1]
          split_ifs <;> first | rfl | omega

theorem sponge_absorb_spec (chunk : Array U32 8#usize) (len : Usize) :
    ∃ ab, R0BlockCopies.sponge_absorb chunk len = ok ab ∧
      ∀ k, ab.val[k]! = if k < 8 ∧ k < len.val then chunk.val[k]! else 0#u32 := by
  obtain ⟨a, ha, hs⟩ := sponge_absorb_loop_spec chunk len 8 0#usize (Array.repeat 16#usize 0#u32) (by simp)
  refine ⟨a, by rw [R0BlockCopies.sponge_absorb]; exact ha, fun k => ?_⟩
  rw [hs k, rep16]
  simp only [show (0#usize : Usize).val = 0 by simp, Nat.zero_le, true_and]

theorem sponge_chunk_loop_spec (input : Array U32 24#usize) (p : Usize) (hp : p.val < 3) :
    ∀ (n : Nat) (lane : Usize) (ch : Array U32 8#usize), lane.val + n = 8 →
      ∃ c', R0BlockCopies.sponge_chunk_loop input p ch lane = ok c' ∧
        ∀ k, c'.val[k]! = if lane.val ≤ k ∧ k < 8 then input.val[8 * p.val + k]! else ch.val[k]!
  | 0, lane, ch, h => by
      refine ⟨ch, ?_, fun k => by rw [if_neg (by omega)]⟩
      rw [R0BlockCopies.sponge_chunk_loop, if_neg (by rw [UScalar.lt_equiv]; scalar_tac)]
  | n + 1, lane, ch, h => by
      have hlt : lane < 8#usize := by rw [UScalar.lt_equiv]; scalar_tac
      have hb : lane.val < (8#usize).val := by simp; omega
      have h8p : (Usize.wrapping_mul 8#usize p).val = 8 * p.val := by rw [umul _ _ (by simp; omega)]; simp
      have hi : (Usize.wrapping_add (Usize.wrapping_mul 8#usize p) lane).val = 8 * p.val + lane.val := by
        rw [uadd _ _ (by rw [h8p]; omega), h8p]
      have hl1 : (Usize.wrapping_add lane 1#usize).val = lane.val + 1 := uadd _ _ (by scalar_tac)
      obtain ⟨c', hc', hs⟩ := sponge_chunk_loop_spec input p hp n (Usize.wrapping_add lane 1#usize)
        (ch.set lane (input.val[8 * p.val + lane.val]!)) (by rw [hl1]; omega)
      refine ⟨c', ?_, fun k => ?_⟩
      · rw [R0BlockCopies.sponge_chunk_loop, if_pos hlt]
        simp only [lift, bind_tc_ok]
        rw [index_ok input _ (by rw [hi]; simp; omega), hi]
        simp only [bind_tc_ok]
        rw [update_ok ch lane _ hb]
        simp only [bind_tc_ok]
        exact hc'
      · rw [hs k, hl1, set_get' ch lane _ hb k]
        split_ifs <;> first | rfl | omega | (subst_vars; rfl)

theorem sponge_chunk_spec (input : Array U32 24#usize) (p : Usize) (hp : p.val < 3) :
    ∃ c, R0BlockCopies.sponge_chunk input p = ok c ∧
      ∀ k, k < 8 → c.val[k]! = input.val[8 * p.val + k]! := by
  obtain ⟨c, hc, hs⟩ := sponge_chunk_loop_spec input p hp 8 0#usize (Array.repeat 8#usize 0#u32) (by simp)
  refine ⟨c, by rw [R0BlockCopies.sponge_chunk]; exact hc, fun k hk => ?_⟩
  rw [hs k, if_pos ⟨by simp, hk⟩]

theorem bc : (R0BlockCopies.BLOCK_CELLS : Usize).val = 256 := by rw [R0BlockCopies.BLOCK_CELLS]; simp

theorem place_loop_spec (p : Usize) (hp : p.val < 3) (block : Array U32 256#usize) :
    ∀ (n : Nat) (i : Usize) (out : Array U32 768#usize), i.val + n = 256 →
      ∃ o', R0BlockCopies.place_block_loop p block out i = ok o' ∧
        ∀ k, o'.val[k]! = if p.val * 256 + i.val ≤ k ∧ k < p.val * 256 + 256
          then block.val[k - p.val * 256]! else out.val[k]!
  | 0, i, out, h => by
      refine ⟨out, ?_, fun k => by rw [if_neg (by omega)]⟩
      rw [R0BlockCopies.place_block_loop, if_neg (by rw [UScalar.lt_equiv, bc]; omega)]
  | n + 1, i, out, h => by
      have hlt : i < R0BlockCopies.BLOCK_CELLS := by rw [UScalar.lt_equiv, bc]; omega
      have hb : i.val < (256#usize).val := by simp; omega
      have hm : (Usize.wrapping_mul p R0BlockCopies.BLOCK_CELLS).val = p.val * 256 := by
        rw [umul _ _ (by rw [bc]; omega), bc]
      have hi : (Usize.wrapping_add (Usize.wrapping_mul p R0BlockCopies.BLOCK_CELLS) i).val = p.val * 256 + i.val := by
        rw [uadd _ _ (by rw [hm]; omega), hm]
      have hib : (Usize.wrapping_add (Usize.wrapping_mul p R0BlockCopies.BLOCK_CELLS) i).val < (768#usize).val := by
        rw [hi]; simp; omega
      have hl1 : (Usize.wrapping_add i 1#usize).val = i.val + 1 := uadd _ _ (by scalar_tac)
      obtain ⟨o', ho', hs⟩ := place_loop_spec p hp block n (Usize.wrapping_add i 1#usize)
        (out.set _ (block.val[i.val]!)) (by rw [hl1]; omega)
      refine ⟨o', ?_, fun k => ?_⟩
      · rw [R0BlockCopies.place_block_loop, if_pos hlt, index_ok block i hb]
        simp only [bind_tc_ok, lift]
        rw [update_ok out _ _ hib]
        simp only [bind_tc_ok]
        exact ho'
      · rw [hs k, hl1, set_get' out _ _ hib k, hi]
        by_cases e : k = p.val * 256 + i.val
        · rw [if_neg (by omega), if_pos e, if_pos (show p.val * 256 + i.val ≤ k ∧ k < p.val * 256 + 256 by omega),
            show k - p.val * 256 = i.val by omega]
        · rw [if_neg e]
          split_ifs <;> first | rfl | omega

#print axioms sponge_init_spec
#print axioms sponge_absorb_spec
#print axioms sponge_chunk_spec
#print axioms place_loop_spec
end R0Z.WriterRefine
