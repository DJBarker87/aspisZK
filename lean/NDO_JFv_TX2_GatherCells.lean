import NDO_JFv_TX2_GatherShape
import Port5Q1_ListCells
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFv_TX2_GatherCells
open Aeneas Aeneas.Std

theorem flat (i : Fin 12) (j : Fin 5) :
    Port4C_BatchInverse.cell (JFv_TX2_GatherShape.flat 12) (5*i.val+j.val)=
      (JFv_TX2_Rows.value i).words[j.val]?.getD 0#u32 := by
  unfold Port4C_BatchInverse.cell JFv_TX2_GatherShape.flat
  have eq := Port5Q1_ListCells.flat_cell
    (fun k => (JFv_TX2_GatherShape.row k).words)
    (fun k => by rfl) (List.range 12) i.val j.val
    (by simpa using i.isLt) j.isLt
  rw [eq,List.getElem_range]
  rw [JFv_TX2_GatherShape.row_eq i.val i.isLt]

theorem node (i : Fin 12) :
    (JFv_TX2_GatherShape.zs 12)[i.val]?.getD 0#u32=(JFv_TX2_Rows.value i).lineZ := by
  simp only [JFv_TX2_GatherShape.zs,List.getElem?_map,List.getElem?_range i.isLt,
    Option.map_some,Option.getD_some,JFv_TX2_GatherShape.row_eq i.val i.isLt]

#print axioms flat
#print axioms node
end AspisR1.JFv_TX2_GatherCells
end
