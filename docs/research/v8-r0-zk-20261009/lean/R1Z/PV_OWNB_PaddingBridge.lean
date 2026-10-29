import R1Z.PV_OWNB_LinkCodec
set_option autoImplicit false
namespace R1Z.PV_OWNB_PaddingBridge
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_Link PV_OWNB_LinkCodec
/-- A view projection, not an actual native mutation. It forgets only padding. -/
def abstractCell (c : Cell) (s : Nat) (v : Link) : Cell :=
 store c s 8 (PV_OWNB_Padding.normalize (PV_OWNB_LinkBytes.encode v) (fun i=>c.contents (s+i)))

theorem exact (c : Cell) (s : Nat) (v : Link) (h:NativeView c s v) :
 PV_OWN_View.Represents codec (abstractCell c s v) s v := by
 unfold abstractCell
 rw [PV_OWNB_Padding.normalization _ _ h.2]
 exact PV_OWN_View.initialized codec c s v h.1

theorem header (c : Cell) (s : Nat) (v : Link) :
 (abstractCell c s v).size=c.size ∧ (abstractCell c s v).alignment=c.alignment ∧
 (abstractCell c s v).owner=c.owner ∧ (abstractCell c s v).live=c.live := ⟨rfl,rfl,rfl,rfl⟩
#print axioms exact
#print axioms header
end R1Z.PV_OWNB_PaddingBridge
