import R1Z.PV_CB3_StagedByteBits
set_option autoImplicit false
namespace R1Z.PV_CB3_StagedByteShape
open Aeneas Aeneas.Std

def tail2 (c d : U8) : BitVec 24 :=
  c.bv.setWidth 24 ||| (((d.bv.setWidth 16) <<< 8).setWidth 24)
def tail3 (b c d : U8) : BitVec 32 :=
  b.bv.setWidth 32 ||| ((tail2 c d <<< 8).setWidth 32)
def assembled (a b c d : U8) : BitVec 32 :=
  a.bv.setWidth 32 ||| (tail3 b c d <<< 8)

/-- Four-byte parser shape, isolated before any arithmetic normalization. -/
theorem source (a b c d : U8) :
    core.num.U32.from_le_bytes (Array.make 4#usize [a,b,c,d]) = (⟨assembled a b c d⟩ : U32) := by
  simp [core.num.U32.from_le_bytes,Array.make,BitVec.fromLEBytes,assembled,tail2,tail3]
#print axioms source
end R1Z.PV_CB3_StagedByteShape
