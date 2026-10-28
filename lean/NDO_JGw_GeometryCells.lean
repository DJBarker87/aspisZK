import NDO_JGp_Shape
import Port5Q1_ListCells
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_GeometryCells
open Aeneas Aeneas.Std

theorem flat (i : Fin 10) (j : Fin 5) :
    Port4C_BatchInverse.cell (JGp_Shape.flat 10) (5*i.val+j.val)=
      (JGp_Rows.value i).words[j.val]?.getD 0#u32 := by
  unfold Port4C_BatchInverse.cell JGp_Shape.flat
  have eq := Port5Q1_ListCells.flat_cell
    (fun k => (JGp_Shape.row k).words)
    (fun k => by rfl) (List.range 10) i.val j.val
    (by simpa using i.isLt) j.isLt
  rw [eq,List.getElem_range]
  rw [JGp_Shape.row_eq i.val i.isLt]

theorem node (i : Fin 10) :
    (JGp_Shape.zs 10)[i.val]?.getD 0#u32=(JGp_Rows.value i).lineZ := by
  simp only [JGp_Shape.zs,List.getElem?_map,List.getElem?_range i.isLt,
    Option.map_some,Option.getD_some,JGp_Shape.row_eq i.val i.isLt]

#print axioms flat
#print axioms node
end AspisR1.JGw_GeometryCells
end
