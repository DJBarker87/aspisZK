import R1CanonicalByteAddress

/-! Canonical representatives of padded duplex addresses embed into the
unbounded byte-string domain. This is a representation fact only; it does not
identify any sampler or shared-oracle security experiment. -/
set_option autoImplicit false
namespace AspisR1.CanonicalAddressEmbedding

open FS2.Duplex
open AspisV8R19.DuplexFrames

abbrev AddrC (L : Nat) := {a : Addr L // CanonicalByteAddress.Canonical a}

def toBytes {L : Nat} (a : AddrC L) : Bytes := a.1.toBytes

theorem toBytes_injective {L : Nat} :
    Function.Injective (toBytes (L := L)) := by
  intro a b hab
  apply Subtype.ext
  have hbytes : a.1.toBytes = b.1.toBytes := hab
  have ha : CanonicalByteAddress.normalize a.1 = a.1 := a.2
  have hb : CanonicalByteAddress.normalize b.1 = b.1 := b.2
  have hnorm : CanonicalByteAddress.normalize a.1 =
      CanonicalByteAddress.normalize b.1 := by
    simp [CanonicalByteAddress.normalize, hbytes]
  exact ha.symm.trans (hnorm.trans hb)

def bytesEmbedding (L : Nat) : AddrC L ↪ Bytes :=
  ⟨toBytes, toBytes_injective⟩

theorem image_length_le {L : Nat} (a : AddrC L) : (toBytes a).length ≤ L :=
  CanonicalByteAddress.length_le a.1

#print axioms toBytes_injective
#print axioms image_length_le

end AspisR1.CanonicalAddressEmbedding
