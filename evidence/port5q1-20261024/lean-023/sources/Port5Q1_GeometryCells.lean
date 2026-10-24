import Port5Q1_GeometryBinding
import Port5Q1_SelectedCells
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q1_GeometryCells
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port5Q1_GeometryBinding
abbrev FP := ZMod AspisCircleGroupOrder.P
theorem line_cells
    (queries : Array U32 22#usize) (start end1 : Usize) (out : verifier.QueryGeometry)
    (order : start.val≤end1.val) (bound : end1.val≤22)
    (lineMeaning : out.line_z.val.map S7JoinBasisMachine.decode=
      ((queries.val.drop start.val).take (end1.val-start.val)).map (fun q => Port5Q1_Domain.lineZ q.val)) :
    ∀ i, i<end1.val-start.val →
      S7JoinBasisMachine.decode (out.line_z.val[i]?.getD 0#u32)=
        Port5Q1_Domain.lineZ (queryAt queries (start.val+i)).val := by
  let selected := Port5Q1_SelectedCells.selected queries start end1
  have selectedLen : selected.length=end1.val-start.val :=
    Port5Q1_SelectedCells.length queries start end1 order bound
  have selectedAt : ∀ i, i<end1.val-start.val → selected[i]?.getD 0#u32=queryAt queries (start.val+i) := by
    intro i hi
    rw [Port5Q1_SelectedCells.get queries start end1 i hi]
    rfl
  intro i hi
  have eq := congrArg (fun xs : List FP => xs[i]?.getD 0) lineMeaning
  rw [Port5Q1_ListCells.map_cell] at eq
  change S7JoinBasisMachine.decode (out.line_z.val[i]?.getD 0#u32)=
    (selected.map (fun q => Port5Q1_Domain.lineZ q.val))[i]?.getD 0 at eq
  rw [List.getElem?_map] at eq
  have get : selected[i]?=some (queryAt queries (start.val+i)) := by
    rw [List.getElem?_eq_getElem (by rw [selectedLen]; exact hi)]
    have := selectedAt i hi
    simpa only [List.getElem?_eq_getElem (by rw [selectedLen]; exact hi),Option.getD_some] using congrArg some this
  rw [get] at eq
  exact eq

theorem inverse_cells
    (queries : Array U32 22#usize) (start end1 : Usize) (out : verifier.QueryGeometry)
    (order : start.val≤end1.val) (bound : end1.val≤22)
    (flat inverse : alloc.vec.Vec U32)
    (flatlen : flat.val.length=5*(end1.val-start.val))
    (values : ∀ j, j<flat.val.length →
      S7JoinBasisMachine.decode (Port4C_BatchInverse.cell inverse.val j)=
        (S7JoinBasisMachine.decode (Port4C_BatchInverse.cell flat.val j))⁻¹)
    (groups : out.inverses.val=(List.range (end1.val-start.val)).map (Port4C_CollectLoop.record inverse))
    (flatMeaning : flat.val.map S7JoinBasisMachine.decode=
      ((queries.val.drop start.val).take (end1.val-start.val)).flatMap (fun q => Port5Q1_Domain.words q.val)) :
    ∀ i, i<end1.val-start.val → ∀ j : Fin 5,
      S7JoinBasisMachine.decode (lane (out.inverses.val[i]?.getD
        (Array.make 5#usize [0#u32,0#u32,0#u32,0#u32,0#u32])) j)=
        ((Port5Q1_Domain.words (queryAt queries (start.val+i)).val)[j.val]?.getD 0)⁻¹ := by
  let selected := Port5Q1_SelectedCells.selected queries start end1
  have selectedLen : selected.length=end1.val-start.val :=
    Port5Q1_SelectedCells.length queries start end1 order bound
  have selectedAt : ∀ i, i<end1.val-start.val → selected[i]?.getD 0#u32=queryAt queries (start.val+i) := by
    intro i hi
    rw [Port5Q1_SelectedCells.get queries start end1 i hi]
    rfl
  intro i hi j
  have groupRead : out.inverses.val[i]?=some (Port4C_CollectLoop.record inverse i) := by
    rw [groups,List.getElem?_map,List.getElem?_range hi]
    rfl
  rw [groupRead,Option.getD_some,lane,Port5Q1_ListCells.record_cell,values (5*i+j.val) (by omega)]
  congr 1
  have eq := congrArg (fun xs : List FP => xs[5*i+j.val]?.getD 0) flatMeaning
  rw [Port5Q1_ListCells.map_cell] at eq
  change S7JoinBasisMachine.decode (Port4C_BatchInverse.cell flat.val (5*i+j.val))=
    (selected.flatMap (fun q => Port5Q1_Domain.words q.val))[5*i+j.val]?.getD 0 at eq
  rw [Port5Q1_ListCells.flat_cell _ (by intro x; rfl) selected i j.val
    (by rw [selectedLen]; exact hi) j.isLt] at eq
  have same : selected[i]=queryAt queries (start.val+i) := by
    simpa only [List.getElem?_eq_getElem (by rw [selectedLen]; exact hi),Option.getD_some] using selectedAt i hi
  rw [same] at eq
  exact eq

#print axioms line_cells
#print axioms inverse_cells
end AspisR1.Port5Q1_GeometryCells
end
