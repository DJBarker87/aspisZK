import R0Z.WriterRefineMerge

/-! The extracted value-aux writer, inner bit loop (copy of pair_trace.rs:401-437;
DESIGN-BUILDER-MODEL §9).  For a base local row b ∈ {0, 2, 4}, bits 0..9 go to
row b, bits 10..19 to row b+1 and bits 20..29 to row b xor 12, column t mod 10. -/
set_option autoImplicit false

namespace R0Z.WriterRefine
open Aeneas Aeneas.Std Result R0WriterCopies

/-- base xor 12 for the three value bases. -/
def xr (b : Nat) : Nat := if b = 0 then 12 else if b = 2 then 14 else 8

/-- The bit index stored at flat cell k of the value rows of base b. -/
def tOf (b k : Nat) : Nat := if k / 16 = b then k % 16 else if k / 16 = b + 1 then 10 + k % 16 else 20 + k % 16

/-- Flat cell k belongs to the bit cells of base b. -/
def InRows (b k : Nat) : Prop := (k / 16 = b ∨ k / 16 = b + 1 ∨ k / 16 = xr b) ∧ k % 16 < 10

instance (b k : Nat) : Decidable (InRows b k) := by unfold InRows; infer_instance

/-- The flat cell where the writer stores bit t of base b. -/
def vidx (b t : Nat) : Nat := (if t < 10 then b else if t < 20 then b + 1 else xr b) * 16 + t % 10

theorem shr_val (x s : U32) (hs : s.val < 32) : (U32.wrapping_shr x s).val = x.val / 2 ^ s.val := by
  show (x.bv >>> (s.val % 32)).toNat = _
  rw [BitVec.toNat_ushiftRight, Nat.mod_eq_of_lt hs, Nat.shiftRight_eq_div_pow]
  rfl

theorem bit_val (x s : U32) (hs : s.val < 32) :
    (U32.wrapping_shr x s &&& 1#u32).val = x.val / 2 ^ s.val % 2 := by
  rw [UScalar.val_and, shr_val x s hs, show (1#u32 : U32).val = 1 by simp, Nat.and_one_is_mod]

theorem xor12 (b : Usize) (hb : b.val = 0 ∨ b.val = 2 ∨ b.val = 4) :
    (b ^^^ 12#usize).val = xr b.val := by
  rw [UScalar.val_xor, show (12#usize : Usize).val = 12 by simp]
  rcases hb with h | h | h <;> rw [h] <;> decide

theorem rows_facts (b t k : Nat) (hb : b = 0 ∨ b = 2 ∨ b = 4) (ht : t < 30) :
    InRows b (vidx b t) ∧ tOf b (vidx b t) = t ∧
      (InRows b k → tOf b k = t → k = vidx b t) := by
  unfold InRows tOf vidx xr
  rcases hb with rfl | rfl | rfl <;> refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega

theorem value_inner (raw : U32) (base : Usize) (hb : base.val = 0 ∨ base.val = 2 ∨ base.val = 4) :
    ∀ (n : Nat) (bit : U32) (block : Array U32 256#usize), bit.val + n = 30 →
      ∃ b', write_value_block_loop0_loop0 block raw base bit = ok b' ∧
        ∀ k, (b'.val[k]!).val = if InRows base.val k ∧ bit.val ≤ tOf base.val k
          then raw.val / 2 ^ tOf base.val k % 2 else (block.val[k]!).val
  | 0, bit, block, h => by
      refine ⟨block, ?_, fun k => ?_⟩
      · rw [write_value_block_loop0_loop0, if_neg (by rw [UScalar.lt_equiv]; scalar_tac)]
      · have : ¬ (InRows base.val k ∧ bit.val ≤ tOf base.val k) := by
          unfold InRows tOf xr; rcases hb with e | e | e <;> rw [e] <;> split_ifs <;> omega
        rw [if_neg this]
  | n + 1, bit, block, h => by
      have hlt : bit < 30#u32 := by rw [UScalar.lt_equiv]; scalar_tac
      have hbit : bit.val < 30 := by omega
      obtain ⟨m, hm, hmv⟩ := WP.spec_imp_exists (UScalar.rem_spec bit (y := 10#u32) (by simp))
      have hmv' : m.val = bit.val % 10 := by rw [hmv]; simp
      have hb1 : (Usize.wrapping_add base 1#usize).val = base.val + 1 := uadd _ _ (by scalar_tac)
      have hx := xor12 base hb
      have hcast : (UScalar.cast .Usize m).val = bit.val % 10 := by
        rw [UScalar.cast_val_eq, hmv']
        exact Nat.mod_eq_of_lt (lt_of_lt_of_le (by omega : bit.val % 10 < 2 ^ 32)
          (by rw [← UScalar.size_def]; exact usize_size_ge))
      have hbit1 : (U32.wrapping_add bit 1#u32).val = bit.val + 1 := by
        rw [U32.wrapping_add_val_eq]; exact Nat.mod_eq_of_lt (by rw [UScalar.size_def]; simp; omega)
      -- the step, for any row value with the right value
      have step : ∀ row : Usize, row.val = (if bit.val < 10 then base.val else if bit.val < 20 then
            base.val + 1 else xr base.val) →
          ∃ b', (do
            let i ← lift (U32.wrapping_shr raw bit)
            let i1 ← lift (Usize.wrapping_mul row 16#usize)
            let i2 ← bit % 10#u32
            let i3 ← lift (UScalar.cast .Usize i2)
            let i4 ← lift (Usize.wrapping_add i1 i3)
            let i5 ← lift (i &&& 1#u32)
            let a ← Array.update block i4 i5
            let bit1 ← lift (U32.wrapping_add bit 1#u32)
            write_value_block_loop0_loop0 a raw base bit1) = ok b' ∧
            ∀ k, (b'.val[k]!).val = if InRows base.val k ∧ bit.val ≤ tOf base.val k
              then raw.val / 2 ^ tOf base.val k % 2 else (block.val[k]!).val := by
        intro row hrow
        have hrow' : row.val ≤ 14 := by
          rw [hrow]; unfold xr; rcases hb with e | e | e <;> rw [e] <;> split_ifs <;> omega
        have h16 : (Usize.wrapping_mul row 16#usize).val = row.val * 16 := umul _ _ (by simp; omega)
        have hidx : (Usize.wrapping_add (Usize.wrapping_mul row 16#usize) (UScalar.cast .Usize m)).val =
            vidx base.val bit.val := by
          rw [uadd _ _ (by rw [h16, hcast]; omega), h16, hcast, hrow]; rfl
        have hi : (Usize.wrapping_add (Usize.wrapping_mul row 16#usize) (UScalar.cast .Usize m)).val <
            (256#usize).val := by
          rw [hidx]; simp; unfold vidx xr; rcases hb with e | e | e <;> rw [e] <;> split_ifs <;> omega
        let v := U32.wrapping_shr raw bit &&& 1#u32
        obtain ⟨b', hb', hs⟩ := value_inner raw base hb n (U32.wrapping_add bit 1#u32)
          (block.set (Usize.wrapping_add (Usize.wrapping_mul row 16#usize) (UScalar.cast .Usize m)) v)
          (by rw [hbit1]; omega)
        refine ⟨b', ?_, fun k => ?_⟩
        · simp only [lift, bind_tc_ok]
          rw [hm]
          simp only [bind_tc_ok]
          rw [update_ok block _ _ hi]
          simp only [bind_tc_ok]
          exact hb'
        · rw [hs k, hbit1, set_get' block _ _ hi k, hidx]
          obtain ⟨r1, r2, r3⟩ := rows_facts base.val bit.val k
            (by rcases hb with e | e | e <;> simp [e]) hbit
          by_cases e : k = vidx base.val bit.val
          · subst e
            rw [if_neg (by omega), if_pos rfl, if_pos ⟨r1, by omega⟩, r2]
            exact bit_val raw bit (by omega)
          · rw [if_neg e]
            by_cases c : InRows base.val k ∧ bit.val + 1 ≤ tOf base.val k
            · rw [if_pos c, if_pos ⟨c.1, by omega⟩]
            · have : ¬ (InRows base.val k ∧ bit.val ≤ tOf base.val k) := by
                rintro ⟨h1, h2⟩
                exact c ⟨h1, by
                  by_contra hc
                  exact e (r3 h1 (by omega))⟩
              rw [if_neg c, if_neg this]
      rw [write_value_block_loop0_loop0, if_pos hlt]
      by_cases t1 : bit < 10#u32
      · rw [if_pos t1]
        simp only [bind_tc_ok]
        exact step base (by rw [if_pos (by rw [UScalar.lt_equiv] at t1; simpa using t1)])
      · rw [if_neg t1]
        have t1' : ¬ bit.val < 10 := by rw [UScalar.lt_equiv] at t1; simpa using t1
        by_cases t2 : bit < 20#u32
        · rw [if_pos t2]
          simp only [bind_tc_ok, lift]
          exact step _ (by rw [hb1, if_neg t1', if_pos (by rw [UScalar.lt_equiv] at t2; simpa using t2)])
        · rw [if_neg t2]
          have t2' : ¬ bit.val < 20 := by rw [UScalar.lt_equiv] at t2; simpa using t2
          simp only [bind_tc_ok, lift]
          exact step _ (by rw [hx, if_neg t1', if_neg t2'])

#print axioms shr_val
#print axioms bit_val
#print axioms rows_facts
#print axioms value_inner
end R0Z.WriterRefine
