import R1Z.PV_Src_PortInternalLoop

/-! Pointwise source semantics of the internal-linear loop. Later writes do
not feed earlier lanes back into another cell; full_sum stays fixed. -/
set_option autoImplicit false
namespace R1Z.PV_Src_PortInternalCells
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortInternalStep PV_Src_PortInternalLoop

theorem cell_set_other (state : State) (full : U64) (atIndex index : Usize)
    (value : U32) (ha : atIndex.val < 16) (hne : index.val ≠ atIndex.val) :
    cell (state.set atIndex value) full index = cell state full index := by
  unfold cell
  rw [BuilderRecordsArray.set_get state atIndex value index.val (by simpa using ha),if_neg hne]

theorem cells (n : Nat) (index : Usize) (state : State) (full : U64)
    (count : index.val+n=16) (j : Fin 16) :
    (steps n index state full).val[j.val]! =
      if j.val < index.val then state.val[j.val]!
      else cell state full (Usize.ofNatCore j.val (by have := j.isLt;scalar_tac)) := by
  induction n generalizing index state with
  | zero =>
    rw [if_pos (by have := j.isLt;omega)]
    rfl
  | succ n ih =>
    have hi : index.val < 16 := by omega
    have hn := BuilderRecordsArray.next_val index (by omega)
    rw [steps,ih _ _ (by rw [hn];omega)]
    by_cases hj : j.val < index.val
    · rw [if_pos (by rw [hn];omega),if_pos hj,
        BuilderRecordsArray.set_get state index _ j.val (by simpa using hi),if_neg (by omega)]
    · rw [if_neg hj]
      by_cases he : j.val=index.val
      · rw [if_pos (by rw [hn];omega),BuilderRecordsArray.set_get state index _ j.val
          (by simpa using hi),if_pos he]
        congr 1
        exact UScalar.eq_of_val_eq (by scalar_tac)
      · rw [if_neg (by rw [hn];omega)]
        apply cell_set_other
        · exact hi
        · scalar_tac

#print axioms cell_set_other
#print axioms cells
end R1Z.PV_Src_PortInternalCells
