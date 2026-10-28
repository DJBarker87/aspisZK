import R1Z.PV_Src_ExternalSumLoop

set_option autoImplicit false
namespace R1Z.PV_Src_ExternalSumCells
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_ExternalSumStep PV_Src_ExternalSumLoop

theorem cells (n : Nat) (s : State) (sums : Sums) (col : Usize)
    (count : col.val+n=4) (j : Fin 4) :
    (steps n s sums col).val[j.val]! = if j.val < col.val then sums.val[j.val]!
      else cell s (Usize.ofNatCore j.val (by have := j.isLt;scalar_tac)) := by
  induction n generalizing sums col with
  | zero =>
    rw [if_pos (by have := j.isLt;omega)]
    rfl
  | succ n ih =>
    have hc : col.val < 4 := by omega
    have hn := BuilderRecordsArray.next_val col (by omega)
    rw [steps,ih _ _ (by rw [hn];omega)]
    by_cases hj : j.val < col.val
    · rw [if_pos (by rw [hn];omega),if_pos hj,
        BuilderRecordsArray.set_get _ _ _ _ (by simpa using hc),if_neg (by omega)]
    · rw [if_neg hj]
      by_cases he : j.val=col.val
      · rw [if_pos (by rw [hn];omega),BuilderRecordsArray.set_get _ _ _ _
          (by simpa using hc),if_pos he]
        congr 1
        exact UScalar.eq_of_val_eq (by scalar_tac)
      · rw [if_neg (by rw [hn];omega)]

#print axioms cells
end R1Z.PV_Src_ExternalSumCells
