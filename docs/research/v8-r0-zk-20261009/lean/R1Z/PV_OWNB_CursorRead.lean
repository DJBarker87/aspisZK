import R1Z.PV_OWNB_Cursor
set_option autoImplicit false
namespace R1Z.PV_OWNB_CursorRead
open PV_OWNB_Cursor PV_OWNB_LinkCodec
 theorem read (q : Cursor) (h:Valid q) (notEnd:q.read<q.length) :
 NativeView q.cell (q.read*8) (q.source q.read) := by
 unfold Valid at h
 exact h.2.2.2.2.2.2.1 q.read (Nat.le_refl _) notEnd

 theorem advance (q : Cursor) (h:Valid q) (notEnd:q.read<q.length) :
 Valid (PV_OWNB_Cursor.advance q) := by
 unfold Valid at h ⊢
 unfold PV_OWNB_Cursor.advance
 refine ⟨h.1,h.2.1,h.2.2.1,by omega,by omega,h.2.2.2.2.2.1,?_,h.2.2.2.2.2.2.2⟩
 intro i hi hil
 exact h.2.2.2.2.2.2.1 i (by omega) hil
#print axioms read
#print axioms advance
end R1Z.PV_OWNB_CursorRead
