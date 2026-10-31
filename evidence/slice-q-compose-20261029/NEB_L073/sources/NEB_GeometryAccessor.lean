import S7OwnedP6QueryRead
import NEB_PureFrame
set_option autoImplicit false
namespace NEB_GeometryAccessor
open Aeneas Aeneas.Std Result S7OwnedP6QueryRead

def PacketDomain (g : QueryGeometry) (index : Usize) : Prop :=
  g.inverses.val.length≤22 ∧ g.start.val≤ index.val ∧
  index.val-g.start.val<g.inverses.val.length

/-- Exact same selected five-word row, full Result and pure readonly frame.
The native pointer/borrow representation remains the root physical
interpretation, rather than an unsupported borrowed-return substitution. -/
theorem result {S Event : Type} (state : S) (g : QueryGeometry) (index : Usize)
    (domain : PacketDomain g index) :
    ∃ row, QueryGeometry.for_query g index=ok row ∧
      g.inverses.val[index.val-g.start.val]?=some row ∧
      NEB_PureFrame.run (Event:=Event) state (QueryGeometry.for_query g index)=ok (row,state,[]) := by
  obtain ⟨row,call,selected⟩ := selected_inverse g index domain.2.1 domain.2.2
  exact ⟨row,call,selected,by rw [call];rfl⟩

/-- The actual constructor/query ordinal establishes the complete local
accessor packet domain. No per-row return or canonicality premise is added. -/
theorem caller (g : QueryGeometry) (index finish : Usize)
    (lo : g.start.val≤ index.val) (hi : index.val<finish.val)
    (length : g.inverses.val.length=finish.val-g.start.val) (cap : finish.val≤22) :
    PacketDomain g index := by
  unfold PacketDomain
  omega

#print axioms result
#print axioms caller
end NEB_GeometryAccessor
