import FJj_TensorCellLanes
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJj_TensorModelAdvance
open Aeneas Aeneas.Std
open FIo_FieldBridge (NQ)
abbrev FK := OraclePortCheckpointAbiC5.K

def expanded (base : Nat → FK) (digit : Array NQ 4#usize) (n e t : Nat) : FK :=
  if t<4*n ∧ e≤t%n then base (t%n)*FJf_QMArray.value digit (t/n) else base t

theorem value (base : Nat → FK) (input : Slice NQ) (digit : Array NQ 4#usize)
    (j n : Usize) (e : Nat) (hn : n.val≤16) (hj : j.val < n.val) (he : j.val+1=e)
    (inv : ∀ t,FJj_QMSlice.value input t=expanded base digit n.val e t) (t : Nat) :
    FJj_TensorCellValue.model input digit j n t=expanded base digit n.val j.val t := by
  have np : 0<n.val := by omega
  have source : FJj_QMSlice.value input j.val=base j.val := by
    rw [inv,expanded]
    simp only [Nat.mod_eq_of_lt hj,if_neg (show ¬(j.val<4*n.val ∧ e≤j.val) by omega)]
  by_cases hit : t<4*n.val ∧ t%n.val=j.val
  · have ds : t/n.val<4 := (Nat.div_lt_iff_lt_mul np).mpr (by omega)
    let s : Fin 4 := ⟨t/n.val,ds⟩
    have eq : j.val+s.val*n.val=t := by
      dsimp only [s]
      rw [←hit.2,Nat.mul_comm]
      exact Nat.mod_add_div t n.val
    rw [←eq,FJj_TensorCellLanes.written input digit j n hn hj s,source]
    rw [eq]
    unfold expanded
    rw [if_pos (show t<4*n.val ∧ j.val≤t%n.val by omega),hit.2]
  · have no : ∀ s : Usize,s.val<4 → (FJj_TensorCell.index j n s).val≠t := by
      intro s hs eq
      rw [FJj_TensorIndex.value j n s hn hj hs] at eq
      apply hit
      constructor
      · have hm : s.val*n.val≤3*n.val := Nat.mul_le_mul_right n.val (by omega)
        omega
      · rw [←eq,Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt hj]
    unfold FJj_TensorCellValue.model
    rw [if_neg (no 3#usize (by decide)),if_neg (no 2#usize (by decide)),
      if_neg (no 1#usize (by decide)),if_neg (no 0#usize (by decide)),inv t]
    unfold expanded
    by_cases ht : t<4*n.val
    · have ne : t%n.val≠j.val := by intro eq;exact hit ⟨ht,eq⟩
      have eq : (e≤t%n.val) ↔ (j.val≤t%n.val) := by omega
      simp only [eq]
    · simp only [ht,false_and,if_false]
#print axioms value
end AspisR1.FJj_TensorModelAdvance
end
