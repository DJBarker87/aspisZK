import IDa_Deployed
import Tx1Q_QueryBridge
import SAQ_CompleteInstall
set_option autoImplicit false
noncomputable section
namespace AspisR1.IDb_Components
open Aeneas Aeneas.Std Result AspisR1Stage2
attribute [local instance] Classical.propDecidable

/-- Every field comes from the adopted query installers at the consumer. -/
def query : Port3_NativeQueryBody.Ops where
  op0 := OraclePortStdBuilder.fromFn
  op1 := fun q => ok (Port4C_RowStd.fromK q)
  op2 := SAQ_Arithmetic.add
  op3 := SAQ_MixedSource.mulE
  op4 := ok 0#u32
  op5 := ok 1#u32
  op6 := AspisR1Qm31ArithmeticProbe.field.M31.sub
  op7 := AspisR1Qm31ArithmeticProbe.field.M31.mul
  op8 := S7Kani3BasisOuter.double
  op9 := SAQ_Arithmetic.mulK
  op10 := fun m => ok (Port4C_RowStd.fromM m)
  op11 := Port4B_Opening.opening
  op12 := Slice.index_usize
  op13 := Array.index_usize
  op14 := Port3_NativeRowFrame.push
  op15 := fun _ _ _ => ok ()
  op16 := SAQ_LineQuery.line
  op17 := FIp_CircleQuery.circle
  op18 := Port5Q1_GeometryBinding.forQuery
  op19 := Port3_QueryStage.mark
  op20 := FIp_DotsAdapter.dots
  op21 := SAQ_Decoder.read
  widePartialEq := FIp_Equality.dictionary

/-- Explicit source geometry leaves, including the same native prefix body. -/
def geometry {C : Type} (indexError : C) : Port3_NativeGeometryBody.Ops C where
  op0 := OraclePortStdBuilder.fromFn
  op1 := OraclePortStdBuilder.iterMap
  op2 := Port4C_GeometryStd.mapError
  op3 := fun pred it f =>
    Port3_BatchStd.anyDefault (core.iter.traits.iterator.IteratorSliceIter _) pred it f
  op4 := fun _ v => ok v.val.isEmpty
  op5 := fun x y => ok (decide (x=y))
  op6 := ok 0#u32
  op7 := ok 1#u32
  op8 := AspisR1Qm31ArithmeticProbe.field.M31.sub
  op9 := AspisR1Qm31ArithmeticProbe.field.M31.mul
  op10 := AspisR1Qm31ArithmeticProbe.field.M31.double
  op11 := SAQ_Inverse.source
  op12 := SAQ_Constructor.fibre indexError
  op13 := Port4C_NativePrefix.verifier.batch_prefix_products
    ⟨AspisR1Qm31ArithmeticProbe.field.M31.mul,ok 1#u32⟩
  op14 := SAQ_Geometry.line
  op15 := SAQ_Geometry.point
  mapIterator := Port4C_CollectStd.mapIterator

/-- This is the exact selection made by FIp then Rc5, before consumer std. -/
def selectedQuery (q : Port3_NativeQueryBody.Ops) :=
  SAQ_Decoder.install {q with
    op20 := FIp_DotsAdapter.dots
    op17 := FIp_CircleQuery.circle
    widePartialEq := FIp_Equality.dictionary}

theorem query_consumer (q : Port3_NativeQueryBody.Ops) :
    Tx1Q_QueryBridge.leaves (selectedQuery q) = query := rfl

theorem geometry_consumer {C : Type} (err : C) (g : Port3_NativeGeometryBody.Ops C) :
    Port5Q1_GeometryTerminal.install (SAQ_Constructor.install err g) = geometry err := rfl

theorem query_fixed : selectedQuery query = query := rfl

theorem geometry_selected {C : Type} (err : C) :
    SAQ_Constructor.install err (geometry err) = geometry err := rfl

theorem query_release : Port3_QueryStage.release
    (Port4C_RowStd.install (Port5Q1_QueryPorts.install query)) = query := rfl

theorem geometry_fixed {C : Type} (err : C) :
    Port5Q1_GeometryTerminal.install (geometry err) = geometry err := rfl

#print axioms query_consumer
#print axioms geometry_consumer
#print axioms query_fixed
#print axioms geometry_selected
#print axioms query_release
#print axioms geometry_fixed
end AspisR1.IDb_Components
end
