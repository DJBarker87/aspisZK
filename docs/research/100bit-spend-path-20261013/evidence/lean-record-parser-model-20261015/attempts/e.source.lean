import R1RecordLengthCodec
import R1ListFieldCodec

/-! A small executable-style model of a tagged, little-endian length-prefixed
record parser. This is a mathematical list model, not an extracted Rust proof. -/
set_option autoImplicit false

namespace AspisR1.RecordParserModel

open FS2.Duplex AspisV8R19.DuplexFrames
open AspisR1.RetainedFieldByteCodec

def parse (tag : AspisV8R19.DuplexFrames.Byte) (size : Nat) (bytes : Bytes) : Option Bytes :=
  if hlen : bytes.length = 5 + size then
    match bytes with
    | [] => none
    | actualTag :: tail =>
        if actualTag = tag then
          match fixedBytes? 4 (tail.take 4) with
          | none => none
          | some wordBytes =>
              if (decodeWordLE wordBytes).val = size then some (tail.drop 4)
              else none
        else none
  else none

theorem take_five_decomposition (bytes : Bytes) (hlen : 5 ≤ bytes.length) :
    bytes.take 5 = [bytes.headD 0] ++ (bytes.drop 1).take 4 := by
  cases bytes with
  | nil => simp at hlen
  | cons b bs => simp [List.take, List.drop]

theorem parse_eq_some_iff (tag : AspisV8R19.DuplexFrames.Byte) (size : Nat) (bytes payload : Bytes)
    (hsize : size < 2^32) :
    parse tag size bytes = some payload ↔
      payload.length = size ∧ bytes = AspisR1.RecordFrameCodec.frame tag payload := by
  constructor
  · intro hp
    unfold parse at hp
    split at hp
    · rename_i hlen
      cases bytes with
      | nil => simp at hlen
      | cons actualTag tail =>
        simp only [List.length_cons] at hlen
        split at hp
        · rename_i htag
          cases hfixed : fixedBytes? 4 (tail.take 4) with
          | none =>
              simp [hfixed] at hp
          | some wordBytes =>
              simp only [hfixed] at hp
              split at hp
              · rename_i hword
                have hdrop : tail.drop 4 = payload := Option.some.inj hp
                have hplen : payload.length = size := by
                  rw [← hdrop, List.length_drop]
                  simp only [List.length_cons] at hlen
                  omega
                have hwordList := AspisR1.ListFieldCodec.fixedBytes?_sound
                  4 (tail.take 4) wordBytes hfixed
                have hlenBytes :
                    List.ofFn wordBytes = AspisR1.PublicInitFrame.lengthBytes size :=
                  (AspisR1.RecordLengthCodec.decodeWordLE_val_eq_iff
                    wordBytes size hsize).mp hword
                have hsegment : tail.take 4 =
                    AspisR1.PublicInitFrame.lengthBytes size := by
                  exact hwordList.symm.trans hlenBytes
                have hprefix : (actualTag :: tail).take 5 =
                    AspisR1.RecordFrameCodec.header tag size := by
                  simp only [List.take_cons, List.take_zero, List.drop_zero]
                  simp [AspisR1.RecordFrameCodec.header, htag, hsegment]
                have hbytes : actualTag :: tail =
                    AspisR1.RecordFrameCodec.frame tag payload := by
                  rw [AspisR1.RecordFrameCodec.frame]
                  have hsplit : actualTag :: tail =
                      (actualTag :: tail).take 5 ++ (actualTag :: tail).drop 5 :=
                    (List.take_append_drop 5 (actualTag :: tail)).symm
                  rw [hsplit, hprefix]
                  have htail : (actualTag :: tail).drop 5 = tail.drop 4 := by rfl
                  rw [htail, hdrop, ← hplen]
                  rfl
                exact ⟨hplen, hbytes⟩
              · simp at hp
        · simp at hp
    · simp at hp
  · rintro ⟨hplen, rfl⟩
    let word : RawWord := ⟨size, by simpa [rawWordCount] using hsize⟩
    have hlen : (AspisR1.RecordFrameCodec.frame tag payload).length = 5 + size := by
      rw [AspisR1.RecordFrameCodec.frame_length, hplen]
    have hbytes :
        AspisR1.PublicInitFrame.lengthBytes size = List.ofFn (encodeWordLE word) :=
      AspisR1.RecordLengthCodec.lengthBytes_eq_encodeWordLE size hsize
    have hfixed : fixedBytes? 4 (AspisR1.PublicInitFrame.lengthBytes size) =
        some (encodeWordLE word) := by
      rw [hbytes, fixedBytes?_ofFn]
    simp [parse, AspisR1.RecordFrameCodec.frame, AspisR1.RecordFrameCodec.header,
      hplen, hlen, hbytes, hfixed, word, decodeWordLE_encodeWordLE]

theorem parse_eq_recordFrame_parse (tag : AspisV8R19.DuplexFrames.Byte) (size : Nat) (bytes : Bytes)
    (hsize : size < 2^32) :
    parse tag size bytes = AspisR1.RecordFrameCodec.parse tag size bytes := by
  cases h : AspisR1.RecordFrameCodec.parse tag size bytes with
  | none =>
      cases hp : parse tag size bytes with
      | none => rfl
      | some payload =>
          have hspec := (parse_eq_some_iff tag size bytes payload hsize).mp hp
          have hframe := (AspisR1.RecordFrameCodec.parse_eq_some_iff
            tag size bytes payload).mpr hspec
          rw [h] at hframe
          contradiction
  | some payload =>
      have hspec := (AspisR1.RecordFrameCodec.parse_eq_some_iff
        tag size bytes payload).mp h
      exact (parse_eq_some_iff tag size bytes payload hsize).mpr hspec

#print axioms take_five_decomposition
#print axioms parse_eq_some_iff
#print axioms parse_eq_recordFrame_parse

end AspisR1.RecordParserModel
