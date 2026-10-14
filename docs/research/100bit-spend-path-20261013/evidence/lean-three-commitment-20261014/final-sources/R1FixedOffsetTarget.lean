import R1TrailingStateFrame

/-! A fixed-offset 32-byte target reader. This is not full wire validation. -/
set_option autoImplicit false
namespace AspisR1.FixedOffsetTarget

open FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.UniformStateFirstHit

def parse {L : Nat} (offset : Nat) (a : Addr L) : Option State :=
  if offset + 32 ≤ a.toBytes.length then
    some (stateOfBytes (a.toBytes.drop offset))
  else none

theorem parse_ofBytes {L : Nat} (offset : Nat) (pre : Bytes) (root : State)
    (tail : Bytes) (hpre : pre.length = offset)
    (hlen : (pre ++ bytes root ++ tail).length ≤ L) :
    parse offset (Addr.ofBytes (pre ++ bytes root ++ tail) hlen) = some root := by
  have htotal : (pre ++ bytes root ++ tail).length = offset + 32 + tail.length := by
    simp [hpre, bytes_length, List.append_assoc, Nat.add_assoc]
  have hfit : offset + 32 ≤ (pre ++ bytes root ++ tail).length := by
    rw [htotal]
    omega
  have hdrop : (pre ++ bytes root ++ tail).drop offset = bytes root ++ tail := by
    rw [List.append_assoc, List.drop_append_of_le_length (by omega),
      List.drop_eq_nil_of_le (by omega), List.nil_append]
  simp only [parse, Addr.toBytes_ofBytes, if_pos hfit]
  rw [hdrop]
  rw [stateOfBytes_bytes]

#print axioms parse
#print axioms parse_ofBytes

end AspisR1.FixedOffsetTarget
