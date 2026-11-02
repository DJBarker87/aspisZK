import R1Z.PV_RunJoin_ByteWordGroups72
import R1Z.PV_RunJoin_MergeArray35
set_option autoImplicit false
namespace R1Z.PV_RunJoin_FourReader73
open Aeneas Aeneas.Std Result
open PV_RunJoin_FlatBytes35 (byte)

/-- Four source reads, with their original error order. Opaque to consumers. -/
def read (s : Slice U8) (a b c d : Usize) : Result U32 := do
  let x ← Slice.index_usize s a
  let y ← Slice.index_usize s b
  let z ← Slice.index_usize s c
  let t ← Slice.index_usize s d
  lift (core.num.U32.from_le_bytes (Array.make 4#usize [x,y,z,t]))

theorem complete (s : Slice U8) (a b c d : Usize) (w : U32)
    (ha : Slice.index_usize s a=ok (byte w ⟨0,by decide⟩))
    (hb : Slice.index_usize s b=ok (byte w ⟨1,by decide⟩))
    (hc : Slice.index_usize s c=ok (byte w ⟨2,by decide⟩))
    (hd : Slice.index_usize s d=ok (byte w ⟨3,by decide⟩)) :
    read s a b c d=ok w := by
  unfold read
  rw [ha];simp only [bind_tc_ok]
  rw [hb];simp only [bind_tc_ok]
  rw [hc];simp only [bind_tc_ok]
  rw [hd];simp only [bind_tc_ok,lift]
  rw [PV_RunJoin_ByteWordGroups72.word]

attribute [irreducible] read
#print axioms read
#print axioms complete
end R1Z.PV_RunJoin_FourReader73
