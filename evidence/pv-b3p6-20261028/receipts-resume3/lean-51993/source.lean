import PV_B3P_PrefixAction224
import PV_B3P_MaskLoopBounds132
namespace PV_B3P_PrefixLoop224
open Aeneas Aeneas.Std PV_B3P_224Prefix PV_B3P_RustResult PV_B3P_PrefixAction224
set_option autoImplicit false

theorem complete_loop (view : prefix224.View) (registry : Registry) (append_index : U64)
    (lambda : aspis_core.field.QM31) (n : Nat) (rows : Rows) (i : Usize)
    (hi : i.val+n = 136) :
    prefix224.copy_rows_loop view registry append_index lambda rows i =
      PV_B3P_HelperState224.run (action view registry append_index lambda) i.val n rows := by
  induction n generalizing rows i with
  | zero =>
    have hb : ¬i < 136#usize := by scalar_tac
    unfold prefix224.copy_rows_loop
    rw [loop.eq_1]
    dsimp only
    simp only [prefix224.copy_rows_loop.body,hb,↓reduceIte,PV_B3P_HelperState224.run]
  | succ n ih =>
    rw [PV_B3P_HelperState224.run]
    have hb : i.val < 136 := by omega
    have hnext := (PV_B3P_MaskLoopBounds132.row_next i (by omega)).1
    have hs := body view registry append_index lambda rows i hb
    cases he : action view registry append_index lambda i.val rows with
    | fail e =>
      unfold prefix224.copy_rows_loop
      rw [loop.eq_1]
      dsimp only
      rw [hs,he]
      rfl
    | div =>
      unfold prefix224.copy_rows_loop
      rw [loop.eq_1]
      dsimp only
      rw [hs,he]
      rfl
    | ok res =>
      cases res with
      | Err e =>
        unfold prefix224.copy_rows_loop
        rw [loop.eq_1]
        dsimp only
        rw [hs,he]
        rfl
      | Ok next =>
        have ht := ih next (Usize.wrapping_add i 1#usize) (by omega)
        unfold prefix224.copy_rows_loop at ht ⊢
        rw [loop.eq_1]
        dsimp only
        rw [hs,he]
        simp only [PV_B3P_PrefixAction224.control,bindR]
        rw [hnext] at ht
        exact ht

#print axioms complete_loop
end PV_B3P_PrefixLoop224
