import R1PublicInitFrame

/-! Exact byte-model codec for a tagged, little-endian length-prefixed record.
This models byte equality and framing only; it does not establish equivalence
to a Rust parser's integer conversion or its error behavior. -/
set_option autoImplicit false

namespace AspisR1.RecordFrameCodec

open FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

def header (tag : Byte) (size : Nat) : Bytes :=
  [tag] ++ AspisR1.PublicInitFrame.lengthBytes size

def frame (tag : Byte) (payload : Bytes) : Bytes :=
  header tag payload.length ++ payload

def parse (tag : Byte) (size : Nat) (bytes : Bytes) : Option Bytes :=
  if bytes.length = 5 + size ∧ bytes.take 5 = header tag size then
    some (bytes.drop 5)
  else none

theorem header_length (tag : Byte) (size : Nat) : (header tag size).length = 5 := by
  simp [header, AspisR1.PublicInitFrame.lengthBytes_length]

theorem frame_length (tag : Byte) (payload : Bytes) :
    (frame tag payload).length = 5 + payload.length := by
  simp [frame, header_length]

theorem parse_frame (tag : Byte) (payload : Bytes) (size : Nat)
    (hsize : payload.length = size) :
    parse tag size (frame tag payload) = some payload := by
  have hlen : (frame tag payload).length = 5 + size := by
    rw [frame_length, hsize]
  have htake : (frame tag payload).take 5 = header tag size := by
    rw [frame, hsize]
    exact List.take_append_of_le_length (by rw [header_length])
  have hdrop : (frame tag payload).drop 5 = payload := by
    rw [frame, hsize]
    rw [List.drop_append_of_le_length (by rw [header_length])]
    rw [List.drop_eq_nil_of_le (by rw [header_length])]
    simp
  unfold parse
  rw [if_pos ⟨hlen, htake⟩]
  exact congrArg some hdrop

theorem parse_sound (tag : Byte) (size : Nat) (bytes payload : Bytes)
    (h : parse tag size bytes = some payload) :
    payload.length = size ∧ bytes = frame tag payload := by
  unfold parse at h
  split at h
  · rename_i hp
    have hdrop : bytes.drop 5 = payload := Option.some.inj h
    have hlen : payload.length = size := by
      have hdropLen : (bytes.drop 5).length = size := by
        rw [List.length_drop, hp.1]
        omega
      rw [hdrop] at hdropLen
      exact hdropLen
    have hbytes : bytes = bytes.take 5 ++ bytes.drop 5 :=
      (List.take_append_drop 5 bytes).symm
    constructor
    · exact hlen
    · rw [hbytes, hp.2, hdrop, ← hlen]
      rfl
  · simp at h

theorem parse_eq_some_iff (tag : Byte) (size : Nat) (bytes payload : Bytes) :
    parse tag size bytes = some payload ↔
      payload.length = size ∧ bytes = frame tag payload := by
  constructor
  · exact parse_sound tag size bytes payload
  · rintro ⟨hsize, rfl⟩
    exact parse_frame tag payload size hsize

theorem zero_tag_empty :
    frame (0 : Byte) [] = AspisR1.PublicInitFrame.emptyRecord := by
  simp [frame, header, AspisR1.PublicInitFrame.emptyRecord,
    AspisR1.PublicInitFrame.lengthBytes]

#print axioms header_length
#print axioms frame_length
#print axioms parse_frame
#print axioms parse_sound
#print axioms parse_eq_some_iff
#print axioms zero_tag_empty

end AspisR1.RecordFrameCodec
