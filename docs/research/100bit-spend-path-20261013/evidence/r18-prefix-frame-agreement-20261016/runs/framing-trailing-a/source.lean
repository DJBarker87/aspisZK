import FS2.DuplexDecode

/-! Generic byte-frame plumbing for a prefix followed by one full state. -/
set_option autoImplicit false
namespace AspisR1.TrailingStateFrame

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment AspisV8R19.DuplexFrames
open AspisV8R19.UniformStateFirstHit
open AspisV8R19.SourceDuplexStep

noncomputable section

def frame (pre : Bytes) (s : State) : Bytes := pre ++ bytes s

theorem frame_injective (pre : Bytes) : Function.Injective (frame pre) := by
  intro s t h
  exact bytes_injective (List.append_cancel_left h)

theorem frame_drop_prefix (pre : Bytes) (s : State) :
    (frame pre s).drop pre.length = bytes s := by
  rw [frame, List.drop_append_of_le_length (by simp)]
  rw [List.drop_eq_nil_of_le (by simp)]
  simp

def frameAddr {L : Nat} (pre : Bytes) (s : State)
    (h : (frame pre s).length ≤ L) : Addr L :=
  Addr.ofBytes (frame pre s) h

def tailState {L : Nat} (a : Addr L) : Option State :=
  if h : 32 ≤ a.toBytes.length then
    some (stateOfBytes (a.toBytes.drop (a.toBytes.length - 32)))
  else none

theorem tailState_frameAddr {L : Nat} (pre : Bytes) (s : State)
    (h : (frame pre s).length ≤ L) :
    tailState (frameAddr pre s h) = some s := by
  have hlen : (frame pre s).length = pre.length + 32 := by
    simp [frame, bytes_length]
  have hlen' : (pre ++ bytes s).length = pre.length + 32 := by
    simp [bytes_length]
  simp only [tailState, frameAddr, Addr.toBytes_ofBytes]
  have h32 : 32 ≤ (frame pre s).length := by rw [hlen]; omega
  simp only [dif_pos h32]
  simp only [frame]
  rw [hlen']
  simp only [Nat.add_sub_cancel_right]
  rw [List.drop_append_of_le_length (by simp)]
  rw [List.drop_eq_nil_of_le (by simp)]
  simpa using (stateOfBytes_bytes s ([] : Bytes))

#print axioms frame_injective
#print axioms frame_drop_prefix
#print axioms tailState_frameAddr

end
end AspisR1.TrailingStateFrame
