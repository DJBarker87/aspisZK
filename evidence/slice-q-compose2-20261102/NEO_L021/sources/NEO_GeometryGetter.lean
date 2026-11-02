import NEB_GeometryAccessor
import Port3_NativeQueryBody
set_option autoImplicit false
namespace NEO_GeometryGetter
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2

-- The cohort query uses op18 rather than an emitted verifier.for_query name.
-- Install the existing exact S7 emitted getter on the same owned fields.
def carrier (g : verifier.QueryGeometry) : S7OwnedP6QueryRead.QueryGeometry :=
 ⟨g.start,g.inverses,g.line_z⟩

def read (g : verifier.QueryGeometry) (i : Usize) : Result (Array U32 5#usize) :=
 S7OwnedP6QueryRead.QueryGeometry.for_query (carrier g) i

def install (ops : Port3_NativeQueryBody.Ops) : Port3_NativeQueryBody.Ops :=
 {ops with op18:=read}

theorem selected {S Event : Type} (s : S) (ops : Port3_NativeQueryBody.Ops)
 (g : verifier.QueryGeometry) (i : Usize)
 (domain : NEB_GeometryAccessor.PacketDomain (carrier g) i) :
 ∃ row, (install ops).op18 g i=ok row ∧
  g.inverses.val[i.val-g.start.val]?=some row ∧
  NEB_PureFrame.run (Event:=Event) s ((install ops).op18 g i)=ok (row,s,[]) := by
 exact NEB_GeometryAccessor.result s (carrier g) i domain

#print axioms selected
end NEO_GeometryGetter
