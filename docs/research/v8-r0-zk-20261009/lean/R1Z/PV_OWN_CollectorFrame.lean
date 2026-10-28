import R1Z.PV_OWN_CollectorCursor
import R1Z.PV_OWN_View
set_option autoImplicit false
namespace R1Z.PV_OWN_CollectorFrame
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_View PV_OWN_CollectorCursor
/-- Future typed reads retain every payload field, not merely the endpoints. -/
theorem unread {T : Type} (codec : Codec T) (cell : Cell) (bytes : Bytes)
 (read write next : Nat) (value : T) (compact:write≤read) (future:read<next)
 (represented:Represents codec cell (next*codec.width) value) :
 Represents codec (store cell (write*codec.width) codec.width bytes) (next*codec.width) value := by
 refine ⟨represented.1,?_⟩
 intro i hi
 rw [show (store cell (write*codec.width) codec.width bytes).contents (next*codec.width+i)=
   cell.contents (next*codec.width+i) from future_byte cell.contents bytes codec.width read write next i compact future]
 exact represented.2 i hi
#print axioms unread
end R1Z.PV_OWN_CollectorFrame
