import Port5Q1_GeometryBinding
import Port5Q1_MapPoint
import Port5Q1_SelectedCells
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q1_GeometryLine
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port5Q1_GeometryBinding
abbrev FP := ZMod AspisCircleGroupOrder.P
attribute [local irreducible] Port5Q1_Domain.lineZ
theorem line_cells
    (queries : Array U32 22#usize) (start end1 : Usize) (out : verifier.QueryGeometry)
    (order : start.val≤end1.val) (bound : end1.val≤22)
    (lineMeaning : out.line_z.val.map S7JoinBasisMachine.decode=
      ((queries.val.drop start.val).take (end1.val-start.val)).map (fun q => Port5Q1_Domain.lineZ q.val)) :
    ∀ i, i<end1.val-start.val →
      S7JoinBasisMachine.decode (out.line_z.val[i]?.getD 0#u32)=
        Port5Q1_Domain.lineZ (queryAt queries (start.val+i)).val := by
  intro i hi
  have len := Port5Q1_SelectedCells.length queries start end1 order bound
  have result := Port5Q1_MapPoint.transfer S7JoinBasisMachine.decode
    (fun q : U32 => Port5Q1_Domain.lineZ q.val) out.line_z.val
    (Port5Q1_SelectedCells.selected queries start end1) 0#u32 0#u32 lineMeaning i (by rw [len]; exact hi)
  rw [Port5Q1_SelectedCells.get queries start end1 i hi] at result
  exact result

#print axioms line_cells
end AspisR1.Port5Q1_GeometryLine
end
