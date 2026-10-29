import R1Z.PV_OWNI_EntryBytes
import Init.Data.UInt.Lemmas
set_option autoImplicit false
namespace R1Z.PV_OWNI_ByteWord
/-- Numeric little-endian active bytes; independent of allocation addresses. -/
def byte (n i : Nat) : UInt8 := UInt8.ofNat ((n/256^i)%256)

theorem u32_injective (a b : Nat) (ha:a<4294967296) (hb:b<4294967296)
 (h:∀ i,i<4 → byte a i=byte b i) : a=b := by
 have h0:=congrArg UInt8.toNat (h 0 (by decide))
 have h1:=congrArg UInt8.toNat (h 1 (by decide))
 have h2:=congrArg UInt8.toNat (h 2 (by decide))
 have h3:=congrArg UInt8.toNat (h 3 (by decide))
 simp only [byte,UInt8.toNat_ofNat'] at h0 h1 h2 h3
 change ((a/1)%256)%256=((b/1)%256)%256 at h0
 change ((a/256)%256)%256=((b/256)%256)%256 at h1
 change ((a/65536)%256)%256=((b/65536)%256)%256 at h2
 change ((a/16777216)%256)%256=((b/16777216)%256)%256 at h3
 omega

theorem row_injective (a b : Nat) (ha:a<1024) (hb:b<1024)
 (h:∀ i,i<8 → byte a i=byte b i) : a=b :=
 u32_injective a b (by omega) (by omega) (fun i hi=>h i (by omega))
#print axioms u32_injective
#print axioms row_injective
end R1Z.PV_OWNI_ByteWord
