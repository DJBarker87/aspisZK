import R1Z.PV_CBM_ValueClassification
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Card
namespace R1Z.PV_CBM_ValueBijection
open PV_CBM_InventoryShape PV_CBM_ValueClassification
set_option autoImplicit false
abbrev Index := (i : Fin 16) × Fin (16 - usedColumns i.val)
abbrev Cell := {cell : Fin 1024 × Fin 16 // 1008 ≤ cell.1.val ∧ free cell.1.val cell.2.val}
noncomputable instance : Fintype Cell := Fintype.ofFinite Cell

def toCell (i : Index) : Cell := by
  let row := 1008+i.1.val
  let column := usedColumns i.1.val+i.2.val
  have hr : row < 1024 := by
    dsimp [row]
    have := i.1.isLt
    omega
  have hc : column < 16 := by
    dsimp [column]
    have := i.2.isLt
    omega
  have hn : ¬ auxUsed row column := by
    dsimp [row,column]
    intro h
    have hp := (valueAux_iff i.1.val _ i.1.isLt).mp h
    omega
  exact ⟨(⟨row,hr⟩,⟨column,hc⟩),by dsimp [row]; omega,
    free_aux row column (by dsimp [row]; omega) hn⟩

theorem toCell_injective : Function.Injective toCell := by
  intro a b h
  have hr := congrArg (fun x : Cell => x.val.1.val) h
  have hc := congrArg (fun x : Cell => x.val.2.val) h
  have hi : a.1 = b.1 := by
    apply Fin.ext
    dsimp [toCell] at hr
    omega
  rcases a with ⟨ai,aj⟩
  rcases b with ⟨bi,bj⟩
  dsimp at hi
  subst bi
  have hj : aj = bj := by
    apply Fin.ext
    dsimp [toCell] at hc
    omega
  subst bj
  rfl

theorem toCell_surjective : Function.Surjective toCell := by
  intro cell
  have hr := cell.prop.1
  have hrmax := cell.val.1.isLt
  have hc := cell.val.2.isLt
  have hn : ¬ auxUsed cell.val.1.val cell.val.2.val := by
    rcases cell.prop.2 with h | h
    · exact False.elim (by have hp := h.1; unfold poseidon at hp; omega)
    · exact h.2
  have hused : usedColumns (cell.val.1.val-1008) ≤ cell.val.2.val := by
    by_contra h
    have hcol : cell.val.2.val < usedColumns (cell.val.1.val-1008) := by omega
    have ha := (valueAux_iff (cell.val.1.val-1008) _ (by omega)).mpr hcol
    have heq : 1008+(cell.val.1.val-1008)=cell.val.1.val := by omega
    rw [heq] at ha
    exact hn ha
  refine ⟨⟨⟨cell.val.1.val-1008, by omega⟩,
    ⟨cell.val.2.val-usedColumns (cell.val.1.val-1008), by
      change cell.val.2.val-usedColumns (cell.val.1.val-1008) < 16-usedColumns (cell.val.1.val-1008)
      omega⟩⟩, ?_⟩
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext <;> dsimp [toCell] <;> omega

noncomputable def equiv : Index ≃ Cell := Equiv.ofBijective toCell ⟨toCell_injective,toCell_surjective⟩

theorem index_cardinal : Fintype.card Index = 131 := by
  simp only [Index, Fintype.card_sigma, Fintype.card_fin]
  decide

theorem cardinal : Fintype.card Cell = 131 := by
  rw [← Fintype.card_congr equiv]
  exact index_cardinal

#print axioms toCell_injective
#print axioms toCell_surjective
#print axioms index_cardinal
#print axioms cardinal
end R1Z.PV_CBM_ValueBijection
