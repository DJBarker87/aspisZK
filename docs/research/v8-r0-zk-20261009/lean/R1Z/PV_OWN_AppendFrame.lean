import R1Z.PV_OWN_CollectorCursor
import R1Z.PV_OWN_View
set_option autoImplicit false
namespace R1Z.PV_OWN_AppendFrame
open PV_OWN_Bytes PV_OWN_View PV_OWN_Heap
/-- Appending a typed cell preserves all earlier typed cells, byte by byte.
A consumer must separately prove its native initialized-length/header update. -/
theorem prior_cell {T : Type} (codec : Codec T) (c : Cell) (newBytes : Bytes)
 (earlier append : Nat) (value : T) (before:earlier<append)
 (repr:Represents codec c (earlier*codec.width) value) :
 Represents codec (store c (append*codec.width) codec.width newBytes) (earlier*codec.width) value := by
 refine ⟨repr.1,?_⟩
 intro i hi
 have gap:=Nat.mul_le_mul_right codec.width before
 simp only [Nat.succ_mul] at gap
 have outside:earlier*codec.width+i<append*codec.width := by omega
 rw [show (store c (append*codec.width) codec.width newBytes).contents (earlier*codec.width+i)=
     c.contents (earlier*codec.width+i) from PV_OWN_Bytes.outside _ _ _ _ _ (Or.inl outside)]
 exact repr.2 i hi
#print axioms prior_cell
end R1Z.PV_OWN_AppendFrame
