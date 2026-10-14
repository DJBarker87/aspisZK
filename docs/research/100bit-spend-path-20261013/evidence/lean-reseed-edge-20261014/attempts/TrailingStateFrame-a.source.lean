import FS2.DuplexDecode

/-! Generic byte-frame plumbing for a prefix followed by one full state. -/
set_option autoImplicit false
namespace AspisR1.TrailingStateFrame

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep

noncomputable section

def frame (prefix : Bytes) (s : State) : Bytes := prefix ++ bytes s

theorem frame_injective (prefix : Bytes) : Function.Injective (frame prefix) := by
  intro s t h
  apply bytes_injective
  exact List.append_cancel_left h

theorem frame_drop_prefix (prefix : Bytes) (s : State) :
    (frame prefix s).drop prefix.length = bytes s := by
  simp [frame, List.drop_append_of_le_length (n := prefix.length) (by simp)]

def frameAddr {L : Nat} (prefix : Bytes) (s : State)
    (h : (frame prefix s).length ≤ L) : Addr L :=
  Addr.ofBytes (frame prefix s) h

def tailState {L : Nat} (a : Addr L) : Option State :=
  if h : 32 ≤ a.toBytes.length then
    some (stateOfBytes (a.toBytes.drop (a.toBytes.length - 32)))
  else none

theorem tailState_frameAddr {L : Nat} (prefix : Bytes) (s : State)
    (h : (frame prefix s).length ≤ L) :
    tailState (frameAddr prefix s h) = some s := by
  have hlen : (frame prefix s).length = prefix.length + 32 := by
    simp [frame, bytes_length]
  simp only [tailState, frameAddr, Addr.toBytes_ofBytes]
  rw [if_pos (by rw [hlen]; omega)]
  rw [hlen]
  simp only [frame]
  rw [List.drop_append_of_le_length (by simp)]
  rw [List.drop_eq_nil_of_le (by simp)]
  simp [stateOfBytes_bytes]

#print axioms frame_injective
#print axioms frame_drop_prefix
#print axioms tailState_frameAddr

end
end AspisR1.TrailingStateFrame
