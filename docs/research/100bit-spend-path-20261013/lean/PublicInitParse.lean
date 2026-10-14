import R1PublicInitFrame
import R1PrefixedStateCodec

/-! Strict initialization parsing for a fixed public-byte statement.
The source's u32 length guard is retained; the prefix includes the literal
P3 domain, length bytes and the full supplied public bytes. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.PublicInitParse
open FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

def parse {L : Nat} (pubBytes : Bytes) (a : Addr L) : Option State :=
  if pubBytes.length < 2^32 then PrefixedStateCodec.parse (PublicInitFrame.pre pubBytes) a
  else none

theorem parse_addr {L : Nat} (pubBytes : Bytes) (hlen : pubBytes.length < 2^32)
    (hL : 75 + pubBytes.length ≤ L) (c1 : State) :
    parse pubBytes (PublicInitFrame.addr pubBytes hL c1) = some c1 := by
  rw [parse, if_pos hlen]
  exact PrefixedStateCodec.parse_frameAddr (PublicInitFrame.pre pubBytes) c1 _

theorem parse_sound {L : Nat} (pubBytes : Bytes) (a : Addr L) (c1 : State)
    (h : parse pubBytes a = some c1) :
    pubBytes.length < 2^32 ∧ a.toBytes =
      PublicInitFrame.domain ++ [0] ++ PublicInitFrame.lengthBytes pubBytes.length ++
        pubBytes ++ bytes c1 := by
  unfold parse at h
  split at h
  · rename_i hlen
    exact ⟨hlen, PrefixedStateCodec.parse_sound (PublicInitFrame.pre pubBytes) a c1 h⟩
  · simp at h

#print axioms parse_addr
#print axioms parse_sound
end AspisR1.PublicInitParse
end
