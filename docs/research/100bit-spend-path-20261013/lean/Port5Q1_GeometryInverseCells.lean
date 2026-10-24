import Port5Q1_GeometryBinding
import Port5Q1_FlatPoint
import Port5Q1_WordShape
import Port5Q1_SelectedCells
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q1_GeometryInverseCells
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port5Q1_GeometryBinding
abbrev FP := ZMod AspisCircleGroupOrder.P
attribute [local irreducible] Port5Q1_Domain.words
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
  intro i hi j
  have groupRead : out.inverses.val[i]?=some (Port4C_CollectLoop.record inverse i) := by
    rw [groups,List.getElem?_map,List.getElem?_range hi]
    rfl
  rw [groupRead,Option.getD_some,lane,Port5Q1_ListCells.record_cell,values (5*i+j.val) (by omega)]
  congr 1
  have len := Port5Q1_SelectedCells.length queries start end1 order bound
  have result := Port5Q1_FlatPoint.transfer (fun q : U32 => Port5Q1_Domain.words q.val)
    Port5Q1_WordShape.length_words flat.val (Port5Q1_SelectedCells.selected queries start end1)
    0#u32 flatMeaning i j.val (by rw [len]; exact hi) j.isLt
  rw [Port5Q1_SelectedCells.get queries start end1 i hi] at result
  exact result

#print axioms inverse_cells
end AspisR1.Port5Q1_GeometryInverseCells
end
