import R1Z.PV_OWNB_FilterFold
set_option autoImplicit false
namespace R1Z.PV_OWNB_FilterComplete
open PV_OWNB_Cursor PV_OWN_Link
/-- On completion no unread tail remains; the output prefix is a typed byte view. -/
theorem complete (keep : Link → Bool) (q : Cursor) (h:Valid q) :
 let final:=PV_OWNB_FilterFold.run keep (q.length-q.read) q
 Valid final ∧ final.read=final.length := by
 unfold Valid at h
 have le:=h.2.2.2.2.1
 have hv:Valid q := h
 refine ⟨PV_OWNB_FilterFold.valid keep _ q hv (by omega),?_⟩
 rw [PV_OWNB_FilterFold.advances,PV_OWNB_FilterFold.length]
 omega
#print axioms complete
end R1Z.PV_OWNB_FilterComplete
