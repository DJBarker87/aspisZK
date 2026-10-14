import FS2.Duplex

/-! Canonical representatives for padded byte addresses. -/
set_option autoImplicit false
namespace AspisR1.CanonicalByteAddress

open FS2.Duplex
open AspisV8R19.DuplexFrames

theorem length_le {L : Nat} (a : Addr L) : a.toBytes.length ≤ L := by
  unfold Addr.toBytes
  calc
    (a.toList.filterMap id).length ≤ a.toList.length := List.length_filterMap_le _ _
    _ = L := a.toList_length

def normalize {L : Nat} (a : Addr L) : Addr L :=
  Addr.ofBytes a.toBytes (length_le a)

theorem toBytes_normalize {L : Nat} (a : Addr L) :
    (normalize a).toBytes = a.toBytes := by
  exact Addr.toBytes_ofBytes _ _

theorem normalize_ofBytes {L : Nat} (bs : Bytes) (h : bs.length ≤ L) :
    normalize (Addr.ofBytes bs h) = Addr.ofBytes bs h := by
  unfold normalize
  rw [Addr.toBytes_ofBytes]
  rfl

theorem normalize_idem {L : Nat} (a : Addr L) :
    normalize (normalize a) = normalize a := by
  exact normalize_ofBytes (a.toBytes) (length_le a)

def Canonical {L : Nat} (a : Addr L) : Prop := normalize a = a

theorem canonical_ofBytes {L : Nat} (bs : Bytes) (h : bs.length ≤ L) :
    Canonical (Addr.ofBytes bs h) :=
  normalize_ofBytes bs h

#print axioms length_le
#print axioms toBytes_normalize
#print axioms normalize_ofBytes
#print axioms normalize_idem
#print axioms canonical_ofBytes

end AspisR1.CanonicalByteAddress
