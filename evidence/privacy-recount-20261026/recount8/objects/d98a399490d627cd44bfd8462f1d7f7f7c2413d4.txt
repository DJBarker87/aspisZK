import R1Z.PV_RunJoin_ByteRead40
import R1Z.PV_RunJoin_CompactStep39
set_option autoImplicit false
namespace R1Z.PV_RunJoin_HighDomain40
open Aeneas Aeneas.Std Result

def HighZero (bytes : List U8) : Prop :=
  ∀ k j : Nat, 32*k+32≤bytes.length → 16≤j → j<32 → bytes[32*k+j]?=some 0#u8

theorem reads (logical : Slice U8) (hz : HighZero logical.val)
    (pos : Usize) (aligned : pos.val%32=0) (bound : pos.val+32≤logical.length)
    (j : Usize) (lo : 16≤j.val) (hi : j.val<32) :
    Slice.index_usize logical (Usize.wrapping_add pos j)=.ok 0#u8 := by
  have cap : logical.length≤Usize.max := logical.property
  have off : (Usize.wrapping_add pos j).val=pos.val+j.val :=
    PV_RunJoin_CompactStep39.offset pos j (by omega)
  have hx : 32*(pos.val/32)=pos.val := by omega
  apply PV_RunJoin_ByteRead40.zero _ _ (by rw [off];omega)
  rw [off,← hx]
  exact hz _ _ (by change 32*(pos.val/32)+32≤logical.length;rw [hx];exact bound) lo hi
#print axioms reads
end R1Z.PV_RunJoin_HighDomain40
