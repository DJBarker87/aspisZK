import Port5Q1_GeometryBinding
import Port5Q1_GeometryCells
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
  refine ⟨hs,nonempty,bound,hlen,?_,?_,?_⟩
  · rw [groups,List.length_map,List.length_range]
  · exact Port5Q1_GeometryLine.line_cells queries start end1 out order bound lineMeaning
  · exact Port5Q1_GeometryInverseCells.inverse_cells queries start end1 out order bound flat inverse flatlen values groups flatMeaning

#print axioms accepted
end AspisR1.Port5Q1_GeometryReads
end
