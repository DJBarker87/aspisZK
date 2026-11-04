import R0Z.WriterRefinePathBlock

/-! The extracted path-aux writer equals the model's path rows 912..1007
(DESIGN-BUILDER-MODEL §9). -/
set_option autoImplicit false

namespace R0Z.WriterRefine
open Aeneas Aeneas.Std Result R0WriterCopies

variable {K : Type} [Field K]

/-- The Rust inputs lift to the model's path records. -/
structure PathLifts (bits : Array U32 24#usize) (cur l r : Array (Array U32 8#usize) 24#usize)
    (C : R0Z.BuilderModel.Cells K) : Prop where
  bit : ∀ v : Fin 24, liftU (K := K) (bits.val[v.val]!) = (C.path v).bit
  current : ∀ (v : Fin 24) (i : Fin 8), liftU (K := K) ((cur.val[v.val]!).val[i.val]!) = (C.path v).current i
  left : ∀ (v : Fin 24) (i : Fin 8), liftU (K := K) ((l.val[v.val]!).val[i.val]!) = (C.path v).left i
  right : ∀ (v : Fin 24) (i : Fin 8), liftU (K := K) ((r.val[v.val]!).val[i.val]!) = (C.path v).right i

theorem rep0 (k : Nat) : (((Array.repeat 1536#usize 0#u32 : Array U32 1536#usize).val[k]! : U32)) = 0#u32 := by
  rw [Array.repeat_val]
  by_cases hk : k < (1536#usize : Usize).val
  · rw [List.getElem!_eq_getElem?_getD, List.getElem?_replicate, if_pos hk]; rfl
  · rw [List.getElem!_eq_getElem?_getD, List.getElem?_replicate, if_neg hk]; rfl

theorem liftU_zero : liftU (K := K) 0#u32 = 0 := by unfold liftU; simp

theorem path_block_model (bits : Array U32 24#usize) (cur l r : Array (Array U32 8#usize) 24#usize)
    (C : R0Z.BuilderModel.Cells K) (hp : PathLifts bits cur l r C) :
    ∃ b, write_path_block bits cur l r = ok b ∧
      ∀ (rr : Nat) (hr : rr < 96) (c : Fin 16), liftU (K := K) (b.val[rr * 16 + c.val]!) =
        R0Z.BuilderModel.auxCell C (912 + rr) c := by
  obtain ⟨b, hb, hs⟩ := path_block_loop bits cur l r 24 0#usize (Array.repeat 1536#usize 0#u32) (by simp)
  refine ⟨b, by rw [write_path_block]; exact hb, fun rr hr c => ?_⟩
  have hc := c.isLt
  rw [hs, rep0]
  simp only [show (0#usize : Usize).val = 0 by simp, Nat.zero_le, true_and]
  unfold R0Z.BuilderModel.auxCell
  rw [dif_pos (show 912 ≤ 912 + rr ∧ 912 + rr < 1008 by omega)]
  have hk16 : (rr * 16 + c.val) / 16 = rr := by omega
  have hlv : lvl (rr * 16 + c.val) = 4 * ((912 + rr - 912) / 16) + (912 + rr) % 16 / 4 := by
    unfold lvl; omega
  have hlv24 : lvl (rr * 16 + c.val) < 24 := by unfold lvl; omega
  by_cases a1 : (912 + rr) % 16 % 4 = 1
  · rw [if_pos a1]
    have hw : InWin (rr * 16 + c.val) := by unfold InWin; omega
    rw [if_pos ⟨hw, hlv24⟩]
    have hpb : pbase (lvl (rr * 16 + c.val)) = rr * 16 := by unfold pbase lvl; omega
    have e : (⟨4 * ((912 + rr - 912) / 16) + (912 + rr) % 16 / 4, by omega⟩ : Fin 24) =
        ⟨lvl (rr * 16 + c.val), hlv24⟩ := Fin.ext hlv.symm
    rw [e]
    unfold PV R0Z.BuilderModel.pathBaseCell
    rw [hpb]
    by_cases c0 : c.val = 0
    · rw [if_pos (by omega), if_pos c0]
      exact hp.bit ⟨_, hlv24⟩
    · rw [if_neg (by omega), if_neg c0]
      by_cases c9 : c.val < 9
      · rw [if_pos (by omega), dif_pos c9]
        rw [show rr * 16 + c.val - rr * 16 - 1 = (⟨c.val - 1, by omega⟩ : Fin 8).val by simp <;> omega]
        exact hp.current ⟨_, hlv24⟩ _
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), dif_neg c9]
        exact liftU_zero
  · rw [if_neg a1]
    by_cases a2 : (912 + rr) % 16 % 4 = 2
    · rw [if_pos a2]
      have hw : InWin (rr * 16 + c.val) := by unfold InWin; omega
      rw [if_pos ⟨hw, hlv24⟩]
      have hpb : pbase (lvl (rr * 16 + c.val)) = rr * 16 - 16 := by unfold pbase lvl; omega
      have e : (⟨4 * ((912 + rr - 912) / 16) + (912 + rr) % 16 / 4, by omega⟩ : Fin 24) =
          ⟨lvl (rr * 16 + c.val), hlv24⟩ := Fin.ext hlv.symm
      rw [e]
      unfold PV R0Z.BuilderModel.pathSuccCell
      rw [hpb, if_neg (by omega), if_neg (by omega)]
      by_cases c8 : c.val < 8
      · rw [if_pos (by omega), dif_pos c8]
        rw [show rr * 16 + c.val - (rr * 16 - 16) - 16 = (⟨c.val, c8⟩ : Fin 8).val by simp <;> omega]
        exact hp.left ⟨_, hlv24⟩ _
      · rw [if_neg (by omega), if_pos (by omega), dif_neg c8]
        rw [show rr * 16 + c.val - (rr * 16 - 16) - 24 = (⟨c.val - 8, by omega⟩ : Fin 8).val by simp <;> omega]
        exact hp.right ⟨_, hlv24⟩ _
    · rw [if_neg a2]
      have hw : ¬ InWin (rr * 16 + c.val) := by unfold InWin; omega
      rw [if_neg (fun h => hw h.1)]
      exact liftU_zero

#print axioms path_block_model
end R0Z.WriterRefine
