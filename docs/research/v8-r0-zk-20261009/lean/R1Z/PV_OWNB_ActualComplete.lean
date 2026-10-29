import R1Z.PV_OWNB_ActualFold
set_option autoImplicit false
namespace R1Z.PV_OWNB_ActualComplete
open PV_OWNB_Cursor PV_OWN_Link PV_OWN_Bytes PV_OWNB_Padding

theorem complete (keep : Link → Bool) (bytes : Nat → Link → Bytes) (q : Cursor) (h:Valid q)
 (copy:∀ i v, Agrees (PV_OWNB_LinkBytes.encode v) (bytes i v)) :
 let final:=PV_OWNB_ActualFold.run keep bytes (q.length-q.read) q
 Valid final ∧ final.read=final.length := by
 have hv:=h
 unfold Valid at h
 have le:=h.2.2.2.2.1
 refine ⟨PV_OWNB_ActualFold.valid keep bytes _ q hv (by omega) copy,?_⟩
 rw [PV_OWNB_ActualFold.advances,PV_OWNB_ActualFold.length]
 omega
#print axioms complete
end R1Z.PV_OWNB_ActualComplete
