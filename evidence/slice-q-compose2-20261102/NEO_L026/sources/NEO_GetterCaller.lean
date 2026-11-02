import NEO_GetterReference
set_option autoImplicit false
namespace NEO_GetterCaller
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2

def Domain (g : verifier.QueryGeometry) (i : Usize) : Prop :=
 NEB_GeometryAccessor.PacketDomain (NEO_GeometryGetter.carrier g) i ∧
 g.line_z.val.length ≤ 22

/-- The actual constructor sizes and reached query ordinal establish every
bound used by the native reference check, including the unused z allocation.
No independently successful borrow is assumed. -/
theorem caller (g : verifier.QueryGeometry) (i finish : Usize)
 (lower : g.start.val ≤ i.val) (upper : i.val < finish.val)
 (inverses : g.inverses.val.length = finish.val-g.start.val)
 (zs : g.line_z.val.length = finish.val-g.start.val) (cap : finish.val ≤ 22) :
 Domain g i := by
 constructor
 · exact NEB_GeometryAccessor.caller (NEO_GeometryGetter.carrier g) i finish lower upper inverses cap
 · omega

/-- Same safe reference, same installed op18 and same selected five-word row,
with the receiver and effect list preserved. -/
theorem complete {S Event : Type} (state : S) (ops : Port3_NativeQueryBody.Ops)
 (g : verifier.QueryGeometry) (i : Usize) (domain : Domain g i) :
 ∃ row, NEO_GetterRef.selected g.start i (alloc.vec.Vec.deref g.inverses)=ok row ∧
 (NEO_GeometryGetter.install ops).op18 g i=ok row ∧
 g.inverses.val[i.val-g.start.val]?=some row ∧
 NEB_PureFrame.run (Event:=Event) state ((NEO_GeometryGetter.install ops).op18 g i)=ok (row,state,[]) := by
 obtain ⟨row,read,selected,frame⟩ := NEO_GeometryGetter.selected (Event:=Event) state ops g i domain.1
 refine ⟨row,?_,read,selected,frame⟩
 rw [NEO_GetterReference.same g i domain.1.2.1]
 exact read

#print axioms caller
#print axioms complete
end NEO_GetterCaller
