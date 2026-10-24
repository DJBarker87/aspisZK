import Port5Q1_QueryPorts
import Port5Q1_LineModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q1_LineInputs
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
open CheckpointBytes5Output (ofE)
open AspisCircleGroupOrder
abbrev FE := OraclePortCheckpointAbiC5.E
abbrev FP := ZMod P
attribute [local irreducible] FoldStoredGeometry.sourceX18 AspisV5FriReleasedLineGeometry.storedLine16X
  FoldRuntimeAlgebra.lineWithInverses FoldGeometryBridge.lx FoldGeometryBridge.ly FoldGeometryBridge.lz

theorem map_x (u : Fin 65536) :
    algebraMap FP FE (FoldGeometryBridge.lx (K:=FP) u)=FoldGeometryBridge.lx (K:=FE) u := by
  simp only [FoldGeometryBridge.lx,Algebra.algebraMap_self_apply]

theorem map_y (u : Fin 65536) :
    algebraMap FP FE (FoldGeometryBridge.ly (K:=FP) u)=FoldGeometryBridge.ly (K:=FE) u := by
  simp only [FoldGeometryBridge.ly,Algebra.algebraMap_self_apply]

theorem map_z (u : Fin 65536) :
    algebraMap FP FE (FoldGeometryBridge.lz (K:=FP) u)=FoldGeometryBridge.lz (K:=FE) u := by
  simp only [FoldGeometryBridge.lz,map_sub,map_mul,map_pow,map_ofNat,map_one,map_x]

/-- Primitive line expression plus its SAME actual inverse/value operands
is precisely the frozen2 queried value. -/
theorem value (ops : Ops) (leaves : Port5Q1_QueryPorts.SessionAPrimitives ops)
    (alpha result : aspis_core.field.wide_exact.WideExact)
    (values : Array aspis_core.field.wide_exact.WideExact 4#usize) (inverse : Array U32 5#usize)
    (data : MatchingSupport.Data FE) (query : Fin 262144)
    (alphaEq : ofE alpha=data.alpha1)
    (valueEq : ∀ t, Port5Q1_OpeningValues.values values t=
      data.V (AspisR1.childIndex (AspisR1.parentIndex (n:=65536) query) t))
    (ix : S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 2)=
      (FoldGeometryBridge.lx (Port5Q1_Domain.parent query.val))⁻¹)
    (iy : S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 3)=
      (FoldGeometryBridge.ly (Port5Q1_Domain.parent query.val))⁻¹)
    (iz : S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 4)=
      (FoldGeometryBridge.lz (Port5Q1_Domain.parent query.val))⁻¹)
    (run : ops.op16 alpha values inverse=ok result) :
    ofE result=AspisV5FriDegreeThreeCorrelatedAgreement.curveValue
      (SecondFoldRestoration.channels data.V) data.alpha1 (AspisR1.parentIndex (n:=65536) query) := by
  let sourceFold := FoldRuntimeAlgebra.lineWithInverses (K:=FE)
  have parentEq : Port5Q1_Domain.parent query.val=AspisR1.parentIndex (n:=65536) query := by
    apply Fin.ext
    change query.val/4%65536=query.val/4
    apply Nat.mod_eq_of_lt
    have := query.isLt
    omega
  rw [leaves.line _ _ _ _ run,alphaEq,funext valueEq,ix,iy,iz]
  simp only [map_inv,map_x,map_y,map_z,parentEq]
  trace_state
  exact Port5Q1_LineModel.fold data.alpha1 data.V _

#print axioms map_x
#print axioms map_y
#print axioms map_z
#print axioms value
end AspisR1.Port5Q1_LineInputs
end
