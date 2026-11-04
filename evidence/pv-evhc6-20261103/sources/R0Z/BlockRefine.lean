import R0Z.BlockWritersExtracted
import R0Z.WriterRefinePathBlock

/-! The extracted generic block writer (copy of write_permutation's cell
layout, pair_trace.rs:268-302; DESIGN-BUILDER-MODEL §10), with the
permutation abstract: `rounds` are its eleven odd-round outputs.
`block_model`: if `rounds` lift to the model block's rows 1..11
(`RoundsOk`, the plug-in point for the Poseidon refinement), the written
block lifts to `blockCell` of the model block, every cell. -/
set_option autoImplicit false

namespace R0Z.WriterRefine
open Aeneas Aeneas.Std Result R0BlockCopies

theorem ends_loop (pre absorb : Array U32 16#usize) :
    ∀ (n : Nat) (lane : Usize) (block : Array U32 256#usize), lane.val + n = 16 →
      ∃ b', write_block_ends_loop pre absorb block lane = ok b' ∧
        ∀ k, b'.val[k]! = if lane.val ≤ k ∧ k < 16 then pre.val[k]!
          else if 192 + lane.val ≤ k ∧ k < 208 then absorb.val[k - 192]! else block.val[k]!
  | 0, lane, block, h => by
      refine ⟨block, ?_, fun k => by rw [if_neg (by omega), if_neg (by omega)]⟩
      rw [write_block_ends_loop, if_neg (by rw [UScalar.lt_equiv]; scalar_tac)]
  | n + 1, lane, block, h => by
      have hlt : lane < 16#usize := by rw [UScalar.lt_equiv]; scalar_tac
      have hb : lane.val < (16#usize).val := by simp; omega
      have h192 : (Usize.wrapping_add 192#usize lane).val = 192 + lane.val := by
        rw [uadd _ _ (by scalar_tac)]; simp
      have hl1 : (Usize.wrapping_add lane 1#usize).val = lane.val + 1 := uadd _ _ (by scalar_tac)
      have hb1 : lane.val < (256#usize).val := by simp; omega
      have hb2 : (Usize.wrapping_add 192#usize lane).val < (256#usize).val := by rw [h192]; simp; omega
      let b1 := block.set lane (pre.val[lane.val]!)
      obtain ⟨b', hb', hs⟩ := ends_loop pre absorb n (Usize.wrapping_add lane 1#usize)
        (b1.set (Usize.wrapping_add 192#usize lane) (absorb.val[lane.val]!)) (by rw [hl1]; omega)
      refine ⟨b', ?_, fun k => ?_⟩
      · rw [write_block_ends_loop, if_pos hlt, index_ok pre lane hb]
        simp only [bind_tc_ok]
        rw [update_ok block lane _ hb1]
        simp only [bind_tc_ok]
        rw [index_ok absorb lane hb]
        simp only [bind_tc_ok, lift]
        rw [update_ok b1 _ _ hb2]
        simp only [bind_tc_ok]
        exact hb'
      · have g2 := set_get' b1 (Usize.wrapping_add 192#usize lane) (absorb.val[lane.val]!) hb2 k
        have g1 := set_get' block lane (pre.val[lane.val]!) hb1 k
        rw [h192] at g2
        rw [hs k, hl1, g2]
        show _ = _
        rw [show b1.val[k]! = (block.set lane (pre.val[lane.val]!)).val[k]! from rfl, g1]
        by_cases e1 : k = lane.val
        · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos e1,
            if_pos (show lane.val ≤ k ∧ k < 16 by omega), e1]
        by_cases e2 : k = 192 + lane.val
        · rw [if_neg (by omega), if_neg (by omega), if_pos e2, if_neg (show ¬ (lane.val ≤ k ∧ k < 16) by omega),
            if_pos (show 192 + lane.val ≤ k ∧ k < 208 by omega), show k - 192 = lane.val by omega]
        rw [if_neg e2, if_neg e1]
        by_cases a : lane.val + 1 ≤ k ∧ k < 16
        · rw [if_pos a, if_pos (show lane.val ≤ k ∧ k < 16 by omega)]
        rw [if_neg a, if_neg (show ¬ (lane.val ≤ k ∧ k < 16) by omega)]
        by_cases b : 192 + (lane.val + 1) ≤ k ∧ k < 208
        · rw [if_pos b, if_pos (show 192 + lane.val ≤ k ∧ k < 208 by omega)]
        rw [if_neg b, if_neg (show ¬ (192 + lane.val ≤ k ∧ k < 208) by omega)]

theorem rounds_inner (rounds : Array (Array U32 16#usize) 11#usize) (r : Usize) (hr : r.val < 11) :
    ∀ (n : Nat) (lane : Usize) (block : Array U32 256#usize), lane.val + n = 16 →
      ∃ b', write_block_rounds_loop0_loop0 rounds block r lane = ok b' ∧
        ∀ k, b'.val[k]! = if (r.val + 1) * 16 + lane.val ≤ k ∧ k < (r.val + 1) * 16 + 16
          then (rounds.val[r.val]!).val[k % 16]! else block.val[k]!
  | 0, lane, block, h => by
      refine ⟨block, ?_, fun k => by rw [if_neg (by omega)]⟩
      rw [write_block_rounds_loop0_loop0, if_neg (by rw [UScalar.lt_equiv]; scalar_tac)]
  | n + 1, lane, block, h => by
      have hlt : lane < 16#usize := by rw [UScalar.lt_equiv]; scalar_tac
      have hb : lane.val < (16#usize).val := by simp; omega
      have hrb : r.val < (11#usize).val := by simpa using hr
      have hr1 : (Usize.wrapping_add r 1#usize).val = r.val + 1 := uadd _ _ (by scalar_tac)
      have hm : (Usize.wrapping_mul (Usize.wrapping_add r 1#usize) 16#usize).val = (r.val + 1) * 16 := by
        rw [umul _ _ (by rw [hr1]; simp; omega), hr1]; simp
      have hi : (Usize.wrapping_add (Usize.wrapping_mul (Usize.wrapping_add r 1#usize) 16#usize) lane).val =
          (r.val + 1) * 16 + lane.val := by rw [uadd _ _ (by rw [hm]; scalar_tac), hm]
      have hib : (Usize.wrapping_add (Usize.wrapping_mul (Usize.wrapping_add r 1#usize) 16#usize) lane).val <
          (256#usize).val := by rw [hi]; simp; omega
      have hl1 : (Usize.wrapping_add lane 1#usize).val = lane.val + 1 := uadd _ _ (by scalar_tac)
      obtain ⟨b', hb', hs⟩ := rounds_inner rounds r hr n (Usize.wrapping_add lane 1#usize)
        (block.set _ ((rounds.val[r.val]!).val[lane.val]!)) (by rw [hl1]; omega)
      refine ⟨b', ?_, fun k => ?_⟩
      · rw [write_block_rounds_loop0_loop0, if_pos hlt, index_ok_gen rounds r hrb]
        simp only [bind_tc_ok]
        rw [index_ok (rounds.val[r.val]!) lane hb]
        simp only [bind_tc_ok, lift]
        rw [update_ok block _ _ hib]
        simp only [bind_tc_ok]
        exact hb'
      · rw [hs k, hl1, set_get' block _ _ hib k, hi]
        by_cases e : k = (r.val + 1) * 16 + lane.val
        · rw [if_neg (by omega), if_pos e, if_pos (show (r.val + 1) * 16 + lane.val ≤ k ∧
            k < (r.val + 1) * 16 + 16 by omega)]
          congr 2; omega
        rw [if_neg e]
        by_cases a : (r.val + 1) * 16 + (lane.val + 1) ≤ k ∧ k < (r.val + 1) * 16 + 16
        · rw [if_pos a, if_pos (show (r.val + 1) * 16 + lane.val ≤ k ∧ k < (r.val + 1) * 16 + 16 by omega)]
        rw [if_neg a, if_neg (show ¬ ((r.val + 1) * 16 + lane.val ≤ k ∧ k < (r.val + 1) * 16 + 16) by omega)]

theorem rounds_outer (rounds : Array (Array U32 16#usize) 11#usize) :
    ∀ (n : Nat) (r : Usize) (block : Array U32 256#usize), r.val + n = 11 →
      ∃ b', write_block_rounds_loop0 rounds block r = ok b' ∧
        ∀ k, b'.val[k]! = if (r.val + 1) * 16 ≤ k ∧ k < 192
          then (rounds.val[k / 16 - 1]!).val[k % 16]! else block.val[k]!
  | 0, r, block, h => by
      refine ⟨block, ?_, fun k => by rw [if_neg (by omega)]⟩
      rw [write_block_rounds_loop0, if_neg (by rw [UScalar.lt_equiv]; scalar_tac)]
  | n + 1, r, block, h => by
      have hlt : r < 11#usize := by rw [UScalar.lt_equiv]; scalar_tac
      have hr11 : r.val < 11 := by omega
      have hr1 : (Usize.wrapping_add r 1#usize).val = r.val + 1 := uadd _ _ (by scalar_tac)
      obtain ⟨b1, hb1, hs1⟩ := rounds_inner rounds r hr11 16 0#usize block (by simp)
      obtain ⟨b', hb', hs⟩ := rounds_outer rounds n (Usize.wrapping_add r 1#usize) b1 (by rw [hr1]; omega)
      refine ⟨b', ?_, fun k => ?_⟩
      · rw [write_block_rounds_loop0, if_pos hlt, hb1]
        simp only [bind_tc_ok, lift]
        exact hb'
      · rw [hs k, hr1, hs1 k]
        simp only [show (0#usize : Usize).val = 0 by simp, Nat.add_zero]
        split_ifs <;> first | rfl | omega | (rw [show k / 16 - 1 = r.val by omega])

/-- The cells of a written block. -/
def BlockVal (pre absorb : Array U32 16#usize) (rounds : Array (Array U32 16#usize) 11#usize) (k : Nat) : U32 :=
  if k < 16 then pre.val[k]! else if k < 192 then (rounds.val[k / 16 - 1]!).val[k % 16]!
  else if k < 208 then absorb.val[k - 192]! else 0#u32

theorem rep256 (k : Nat) : (((Array.repeat 256#usize 0#u32 : Array U32 256#usize).val[k]! : U32)) = 0#u32 := by
  rw [Array.repeat_val]
  by_cases hk : k < (256#usize : Usize).val
  · rw [List.getElem!_eq_getElem?_getD, List.getElem?_replicate, if_pos hk]; rfl
  · rw [List.getElem!_eq_getElem?_getD, List.getElem?_replicate, if_neg hk]; rfl

theorem block_spec (pre absorb : Array U32 16#usize) (rounds : Array (Array U32 16#usize) 11#usize) :
    ∃ b, write_block pre absorb rounds = ok b ∧ ∀ k, b.val[k]! = BlockVal pre absorb rounds k := by
  obtain ⟨b1, hb1, hs1⟩ := ends_loop pre absorb 16 0#usize (Array.repeat 256#usize 0#u32) (by simp)
  obtain ⟨b2, hb2, hs2⟩ := rounds_outer rounds 11 0#usize b1 (by simp)
  refine ⟨b2, ?_, fun k => ?_⟩
  · rw [write_block, write_block_ends, hb1]
    simp only [bind_tc_ok]
    rw [write_block_rounds]
    exact hb2
  · rw [hs2 k, hs1 k, rep256]
    simp only [show (0#usize : Usize).val = 0 by simp, Nat.zero_le, true_and, Nat.add_zero, Nat.zero_add]
    unfold BlockVal
    by_cases a : k < 16
    · rw [if_neg (by omega), if_pos a, if_pos a]
    by_cases b : k < 192
    · rw [if_pos ⟨by omega, b⟩, if_neg a, if_pos b]
    rw [if_neg (by omega), if_neg a, if_neg a, if_neg b]
    by_cases c : k < 208
    · rw [if_pos ⟨by omega, c⟩, if_pos c]
    · rw [if_neg (by omega), if_neg c]

/-! ### Against the model block -/

variable {K : Type} [Field K]

/-- The plug-in point for the Poseidon refinement: the rounds lift to the
model block's rows 1..11, i.e. to the canonical transitions. -/
def RoundsOk (rounds : Array (Array U32 16#usize) 11#usize) (B : R0Z.BuilderModel.BlockIn K) : Prop :=
  ∀ (r : Nat) (i : Fin 16), r < 11 → liftU (K := K) ((rounds.val[r]!).val[i.val]!) =
    R0Z.BuilderModel.blockIter B (r + 1) i

/-- The pre-state and absorption lift to the model block. -/
structure EndsLift (pre absorb : Array U32 16#usize) (B : R0Z.BuilderModel.BlockIn K) : Prop where
  pre : ∀ i : Fin 16, liftU (K := K) (pre.val[i.val]!) = B.pre i
  absorb : ∀ i : Fin 16, liftU (K := K) (absorb.val[i.val]!) = B.absorb i

theorem block_model (pre absorb : Array U32 16#usize) (rounds : Array (Array U32 16#usize) 11#usize)
    (B : R0Z.BuilderModel.BlockIn K) (he : EndsLift pre absorb B) (hr : RoundsOk rounds B) :
    ∃ b, write_block pre absorb rounds = ok b ∧
      ∀ (l c : Fin 16), liftU (K := K) (b.val[l.val * 16 + c.val]!) = R0Z.BuilderModel.blockCell B l.val c := by
  obtain ⟨b, hb, hs⟩ := block_spec pre absorb rounds
  refine ⟨b, hb, fun l c => ?_⟩
  have hc := c.isLt
  have hl := l.isLt
  rw [hs]
  unfold BlockVal R0Z.BuilderModel.blockCell
  by_cases l0 : l.val = 0
  · rw [if_pos (by omega), if_pos (by omega)]
    rw [show l.val * 16 + c.val = c.val by rw [l0]; omega, l0]
    exact he.pre c
  rw [if_neg (by omega)]
  by_cases l11 : l.val < 12
  · rw [if_pos (by omega), if_pos l11]
    obtain ⟨r, hr'⟩ : ∃ r, l.val = r + 1 := ⟨l.val - 1, by omega⟩
    rw [show (l.val * 16 + c.val) / 16 - 1 = r by omega, show (l.val * 16 + c.val) % 16 = c.val by omega, hr']
    exact hr r c (by omega)
  rw [if_neg (by omega), if_neg l11]
  by_cases l12 : l.val = 12
  · rw [if_pos (by omega), if_pos l12, show l.val * 16 + c.val - 192 = c.val by omega]
    exact he.absorb c
  rw [if_neg (by omega), if_neg l12]
  unfold liftU; simp

#print axioms ends_loop
#print axioms rounds_inner
#print axioms rounds_outer
#print axioms block_spec
#print axioms block_model
end R0Z.WriterRefine
