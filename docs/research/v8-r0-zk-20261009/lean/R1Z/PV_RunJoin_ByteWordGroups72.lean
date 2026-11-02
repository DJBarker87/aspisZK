import R1Z.PV_RunJoin_ByteArrayFour72
import R1Z.PV_RunJoin_ByteWord72
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ByteWordGroups72
open Aeneas Aeneas.Std
open PV_RunJoin_FlatBytes35 (byte)

theorem array (w : U32) : Array.make 4#usize
    [byte w ⟨0,by decide⟩,byte w ⟨1,by decide⟩,byte w ⟨2,by decide⟩,byte w ⟨3,by decide⟩]=
    core.num.U32.to_le_bytes w :=
  PV_RunJoin_ByteArrayFour72.complete (core.num.U32.to_le_bytes w)

theorem word (w : U32) : core.num.U32.from_le_bytes (Array.make 4#usize
    [byte w ⟨0,by decide⟩,byte w ⟨1,by decide⟩,byte w ⟨2,by decide⟩,byte w ⟨3,by decide⟩])=w := by
  rw [array,PV_RunJoin_ByteWord72.complete]

#print axioms array
#print axioms word
end R1Z.PV_RunJoin_ByteWordGroups72
