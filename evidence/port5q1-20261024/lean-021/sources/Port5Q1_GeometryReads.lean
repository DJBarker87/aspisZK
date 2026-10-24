import Port5Q1_GeometryBinding
import Port5Q1_SelectedCells
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q1_GeometryReads
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port3_NativeGeometryBody Port5Q1_GeometryBinding
abbrev FP := ZMod AspisCircleGroupOrder.P
variable {CoreError : Type}
theorem accepted (ops : Ops CoreError)
    (leaves : Port5Q1_GeometryCanonical.SessionAPrimitives ops)
    (domain : Port5Q1_Domain.SessionADomain ops)
    (multiply : ops.op9=AspisR1Qm31ArithmeticProbe.field.M31.mul)
    (one : ops.op7=ok (1#u32))
    (inverseLeaf : ops.op11=Port4C_InverseExecution.inverse_owned)
    (queries : Array U32 22#usize) (start end1 : Usize) (out : verifier.QueryGeometry)
    (nonempty : start.val<end1.val)
    (run : Port3_GeometryStage.geometry (Port5Q1_GeometryTerminal.install ops)
      queries start end1=ok (.Ok out)) : Binding queries start end1 out := by
  obtain ⟨flat,inverse,hs,hlen,flatlen,canon,nonzero,invlen,values,groups,flatMeaning,lineMeaning⟩ :=
    Port5Q1_GeometryModel.for_range ops leaves domain multiply one inverseLeaf queries start end1 out nonempty run
  have range := Port4C_GeometryRange.accepted_range (Port5Q1_GeometryTerminal.install ops)
    queries start end1 out run
  obtain ⟨_,order,bound,_,_⟩ := range
  let selected := Port5Q1_SelectedCells.selected queries start end1
  have selectedLen : selected.length=end1.val-start.val :=
    Port5Q1_SelectedCells.length queries start end1 order bound
  have selectedAt : ∀ i, i<end1.val-start.val → selected[i]?.getD 0#u32=queryAt queries (start.val+i) := by
    intro i hi
    rw [Port5Q1_SelectedCells.get queries start end1 i hi]
    rfl
  refine ⟨hs,nonempty,bound,hlen,?_,?_,?_⟩
  · rw [groups,List.length_map,List.length_range]
  · intro i hi
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
  · intro i hi j
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

#print axioms accepted
end AspisR1.Port5Q1_GeometryReads
end
