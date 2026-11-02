import NEO_CellRef.Funs
import NCI_GetterModel
import NEB_PureFrame
import Port3_NativeQueryBody
set_option autoImplicit false
namespace NEO_CellReference
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2

def install (ops : Port3_NativeQueryBody.Ops) : Port3_NativeQueryBody.Ops :=
 {ops with op12:=Slice.index_usize,op13:=Array.index_usize}

/-- The independent reference returns the exact selected cell for every raw
carrier. All invalid bounds remain outside this caller-established domain. -/
theorem slice {T : Type} (xs : Slice T) (i : Usize) (bound : i.val < xs.val.length) :
 NEO_CellRef.cell xs i = ok (xs.val[i.val]'bound) :=
 NCI_GetterModel.slice_get xs i bound

theorem array {T : Type} {n : Usize} (xs : Array T n) (i : Usize)
 (bound : i.val < xs.val.length) :
 NEO_CellRef.cell xs.to_slice i=Array.index_usize xs i := by
 rw [slice xs.to_slice i bound,NCI_GetterModel.array_get xs i bound]
 rfl

theorem basis {S Event : Type} (s : S) (ops : Port3_NativeQueryBody.Ops)
 (xs : Array U32 256#usize) (i : Usize) (bound : i.val < xs.val.length) :
 (install ops).op13 xs i=NEO_CellRef.cell xs.to_slice i ∧
 NEB_PureFrame.run (Event:=Event) s ((install ops).op13 xs i)=
  ok (xs.val[i.val]'bound,s,[]) := by
 constructor
 · exact (array xs i bound).symm
 · exact NEB_PureFrame.successful s _ _ (NCI_GetterModel.array_get xs i bound)

theorem accumulated {S Event : Type} (s : S) (ops : Port3_NativeQueryBody.Ops)
 (xs : Slice aspis_core.field.QM31) (i : Usize) (bound : i.val < xs.val.length) :
 (install ops).op12 xs i=NEO_CellRef.cell xs i ∧
 NEB_PureFrame.run (Event:=Event) s ((install ops).op12 xs i)=
  ok (xs.val[i.val]'bound,s,[]) := by
 constructor
 · rfl
 · exact NEB_PureFrame.successful s _ _ (NCI_GetterModel.slice_get xs i bound)

#print axioms slice
#print axioms array
#print axioms basis
#print axioms accumulated
end NEO_CellReference
