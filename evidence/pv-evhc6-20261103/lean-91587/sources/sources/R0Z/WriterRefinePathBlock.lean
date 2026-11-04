import R0Z.WriterRefinePath
import R0Z.WriterRefineOccRow

/-! The extracted 24-level path-aux writer computes the model's path rows
912..1007 cell by cell (DESIGN-BUILDER-MODEL §9). -/
set_option autoImplicit false

namespace R0Z.WriterRefine
open Aeneas Aeneas.Std Result R0WriterCopies

theorem index_ok_gen {α : Type} [Inhabited α] {n : Usize} (v : Array α n) (i : Usize) (h : i.val < n.val) :
    Array.index_usize v i = ok (v.val[i.val]!) := by
  unfold Array.index_usize
  have hl : i.val < v.val.length := by rw [v.property]; exact h
  rw [Array.getElem?_Usize_eq, List.getElem?_eq_getElem hl, List.getElem!_eq_getElem?_getD,
    List.getElem?_eq_getElem hl]
  rfl

/-- First flat cell of level l's window (its base row). -/
def pbase (l : Nat) : Nat := (16 * (l / 4) + 1 + 4 * (l % 4)) * 16

/-- The level whose window contains flat cell k. -/
def lvl (k : Nat) : Nat := 4 * (k / 256) + (k / 16 % 16) / 4

/-- k lies in some level's two-row window. -/
def InWin (k : Nat) : Prop := (k / 16 % 16 % 4 = 1 ∨ k / 16 % 16 % 4 = 2) ∧ k < 1536

instance (k : Nat) : Decidable (InWin k) := by unfold InWin; infer_instance

theorem win_iff (l k : Nat) (hl : l < 24) :
    (pbase l ≤ k ∧ k < pbase l + 32) ↔ (InWin k ∧ lvl k = l) := by
  unfold pbase InWin lvl
  constructor
  · intro h; omega
  · intro h; omega

/-- The cell a level writes (path_level's formula). -/
def PV (bit : U32) (cur l r : Array U32 8#usize) (lev : Nat) (dflt : U32) (k : Nat) : U32 :=
  if k = pbase lev then bit
  else if pbase lev + 1 ≤ k ∧ k < pbase lev + 9 then cur.val[k - pbase lev - 1]!
  else if pbase lev + 16 ≤ k ∧ k < pbase lev + 24 then l.val[k - pbase lev - 16]!
  else if pbase lev + 24 ≤ k ∧ k < pbase lev + 32 then r.val[k - pbase lev - 24]!
  else dflt

theorem PV_out (bit : U32) (cur l r : Array U32 8#usize) (lev : Nat) (dflt : U32) (k : Nat)
    (hk : ¬ (pbase lev ≤ k ∧ k < pbase lev + 32)) : PV bit cur l r lev dflt k = dflt := by
  unfold PV
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem path_block_loop (bits : Array U32 24#usize) (cur l r : Array (Array U32 8#usize) 24#usize) :
    ∀ (n : Nat) (lev : Usize) (buf : Array U32 1536#usize), lev.val + n = 24 →
      ∃ b', write_path_block_loop bits cur l r buf lev = ok b' ∧
        ∀ k, b'.val[k]! = if InWin k ∧ lev.val ≤ lvl k ∧ lvl k < 24 then
          PV (bits.val[lvl k]!) (cur.val[lvl k]!) (l.val[lvl k]!) (r.val[lvl k]!) (lvl k) (buf.val[k]!) k
          else buf.val[k]!
  | 0, lev, buf, h => by
      refine ⟨buf, ?_, fun k => by rw [if_neg (by omega)]⟩
      rw [write_path_block_loop, if_neg (by rw [UScalar.lt_equiv]; scalar_tac)]
  | n + 1, lev, buf, h => by
      have hlt : lev < 24#usize := by rw [UScalar.lt_equiv]; scalar_tac
      have hl24 : lev.val < 24 := by omega
      have hb : lev.val < (24#usize).val := by simpa using hl24
      have hl1 : (Usize.wrapping_add lev 1#usize).val = lev.val + 1 := uadd _ _ (by scalar_tac)
      obtain ⟨b1, hb1, hs1⟩ := path_level buf lev hl24 (bits.val[lev.val]!) (cur.val[lev.val]!)
        (l.val[lev.val]!) (r.val[lev.val]!)
      obtain ⟨b', hb', hs⟩ := path_block_loop bits cur l r n (Usize.wrapping_add lev 1#usize) b1
        (by rw [hl1]; omega)
      have hs1' : ∀ k, b1.val[k]! = PV (bits.val[lev.val]!) (cur.val[lev.val]!) (l.val[lev.val]!)
          (r.val[lev.val]!) lev.val (buf.val[k]!) k := fun k => by rw [hs1 k]; rfl
      refine ⟨b', ?_, fun k => ?_⟩
      · rw [write_path_block_loop, if_pos hlt, index_ok bits lev hb, index_ok_gen cur lev hb,
          index_ok_gen l lev hb, index_ok_gen r lev hb]
        simp only [bind_tc_ok]
        rw [hb1]
        simp only [bind_tc_ok, lift]
        exact hb'
      · rw [hs k, hl1]
        have w := win_iff lev.val k hl24
        by_cases e : InWin k ∧ lvl k = lev.val
        · rw [if_neg (by omega), if_pos ⟨e.1, by omega, by omega⟩, hs1' k, e.2]
        · have hout : ¬ (pbase lev.val ≤ k ∧ k < pbase lev.val + 32) := fun h => e (w.1 h)
          rw [hs1' k, PV_out _ _ _ _ _ _ _ hout]
          by_cases g : InWin k ∧ lev.val + 1 ≤ lvl k ∧ lvl k < 24
          · rw [if_pos g, if_pos ⟨g.1, by omega, g.2.2⟩]
          · have : ¬ (InWin k ∧ lev.val ≤ lvl k ∧ lvl k < 24) := by
              rintro ⟨a, b, c⟩
              exact g ⟨a, by
                by_contra hc
                exact e ⟨a, by omega⟩, c⟩
            rw [if_neg g, if_neg this]

#print axioms win_iff
#print axioms path_block_loop
end R0Z.WriterRefine
