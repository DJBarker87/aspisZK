import R1PublicInitFrame

/-! Exact byte-model codec for a tagless little-endian length-prefixed frame.
The payload follows its four-byte length directly. This is distinct from the
tagged semantic-record frame and does not establish a Rust parser refinement. -/
set_option autoImplicit false

namespace AspisR1.LengthFrameCodec

open FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

def frame (payload : Bytes) : Bytes :=
  AspisR1.PublicInitFrame.lengthBytes payload.length ++ payload

def parse (size : Nat) (bytes : Bytes) : Option Bytes :=
  if bytes.length = 4 + size ∧
      bytes.take 4 = AspisR1.PublicInitFrame.lengthBytes size then
    some (bytes.drop 4)
  else none

theorem frame_length (payload : Bytes) :
    (frame payload).length = 4 + payload.length := by
  simp [frame, AspisR1.PublicInitFrame.lengthBytes_length]

theorem parse_frame (payload : Bytes) (size : Nat)
    (hsize : payload.length = size) :
    parse size (frame payload) = some payload := by
  have hlen : (frame payload).length = 4 + size := by
    rw [frame_length, hsize]
  have htake : (frame payload).take 4 =
      AspisR1.PublicInitFrame.lengthBytes size := by
    rw [frame, hsize]
    exact List.take_append_of_le_length (by
      rw [AspisR1.PublicInitFrame.lengthBytes_length])
  have hdrop : (frame payload).drop 4 = payload := by
    rw [frame, hsize]
    rw [List.drop_append_of_le_length (by
      rw [AspisR1.PublicInitFrame.lengthBytes_length])]
    rw [List.drop_eq_nil_of_le (by
      rw [AspisR1.PublicInitFrame.lengthBytes_length])]
    simp
  unfold parse
  rw [if_pos ⟨hlen, htake⟩]
  exact congrArg some hdrop

theorem parse_sound (size : Nat) (bytes payload : Bytes)
    (h : parse size bytes = some payload) :
    payload.length = size ∧ bytes = frame payload := by
  unfold parse at h
  split at h
  · rename_i hp
    have hdrop : bytes.drop 4 = payload := Option.some.inj h
    have hlen : payload.length = size := by
      have hdropLen : (bytes.drop 4).length = size := by
        rw [List.length_drop, hp.1]
        omega
      rw [hdrop] at hdropLen
      exact hdropLen
    have hbytes : bytes = bytes.take 4 ++ bytes.drop 4 :=
      (List.take_append_drop 4 bytes).symm
    constructor
    · exact hlen
    · rw [hbytes, hp.2, hdrop, ← hlen]
      rfl
  · simp at h

theorem parse_eq_some_iff (size : Nat) (bytes payload : Bytes) :
    parse size bytes = some payload ↔
      payload.length = size ∧ bytes = frame payload := by
  constructor
  · exact parse_sound size bytes payload
  · rintro ⟨hsize, rfl⟩
    exact parse_frame payload size hsize

#print axioms frame_length
#print axioms parse_frame
#print axioms parse_sound
#print axioms parse_eq_some_iff

end AspisR1.LengthFrameCodec
