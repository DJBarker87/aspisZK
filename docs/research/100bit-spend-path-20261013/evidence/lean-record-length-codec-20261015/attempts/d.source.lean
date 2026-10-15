import R1RetainedFieldByteCodec
import R1PublicInitFrame
import R1RecordFrameCodec

/-! Four-byte length-field conversion plumbing for the mathematical frame
codec. This does not claim an extracted Rust parser refinement. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RecordLengthCodec

open FS2.Duplex AspisV8R19.DuplexFrames
open AspisR1.RetainedFieldByteCodec

/-- The public length encoder is the same four-byte little-endian codec. -/
theorem lengthBytes_eq_encodeWordLE (n : Nat) (hn : n < 2^32) :
    AspisR1.PublicInitFrame.lengthBytes n =
      List.ofFn (encodeWordLE (⟨n, by simpa [rawWordCount] using hn⟩ : RawWord)) := by
  unfold AspisR1.PublicInitFrame.lengthBytes
  apply congrArg List.ofFn
  funext j
  fin_cases j <;> apply Fin.ext <;>
    norm_num [encodeWordLE, AspisR1.PublicInitFrame.lengthBytes,
      rawWordCount] <;> rfl

/-- Decoding the four bytes gives exactly the encoded natural length. -/
theorem decodeWordLE_val_eq_iff (bytes : WordBytes) (n : Nat) (hn : n < 2^32) :
    (decodeWordLE bytes).val = n ↔
      List.ofFn bytes = AspisR1.PublicInitFrame.lengthBytes n := by
  let word : RawWord := ⟨n, by simpa [rawWordCount] using hn⟩
  constructor
  · intro h
    have hword : decodeWordLE bytes = word := Fin.ext h
    have henc := congrArg encodeWordLE hword
    rw [encodeWordLE_decodeWordLE] at henc
    have hbytes : bytes = encodeWordLE word := henc
    have hlist : List.ofFn bytes = List.ofFn (encodeWordLE word) :=
      congrArg List.ofFn hbytes
    rw [lengthBytes_eq_encodeWordLE n hn]
    exact hlist
  · intro h
    have hbytes : bytes = encodeWordLE word :=
      List.ofFn_injective (by
        rw [h, lengthBytes_eq_encodeWordLE n hn])
    rw [hbytes, decodeWordLE_encodeWordLE]

/-- Rust-style mathematical framing check: total size, tag byte, and a
four-byte little-endian decoded size. -/
def rustParse (tag : AspisV8R19.DuplexFrames.Byte) (size : Nat) (bytes : Bytes) : Option Bytes :=
  if bytes.length = 5 + size ∧ bytes.head? = some tag then
    (fixedBytes? 4 ((bytes.drop 1).take 4)).bind fun wordBytes =>
      if (decodeWordLE wordBytes).val = size then some (bytes.drop 5) else none
  else none

private theorem fixedBytes?_toList {xs : List AspisV8R19.DuplexFrames.Byte} {wordBytes : WordBytes}
    (h : fixedBytes? 4 xs = some wordBytes) : List.ofFn wordBytes = xs := by
  unfold fixedBytes? at h
  split at h
  · rename_i hlen
    injection h with hfun
    subst wordBytes
    apply List.ext_getElem
    · simp [List.length_ofFn, hlen]
    · intro i hi1 hi2
      interval_cases i <;> simp [List.ofFn, hlen]
  · simp at h

private theorem drop_take_header (tag : AspisV8R19.DuplexFrames.Byte) (size : Nat)
    (bytes : Bytes) (hlen : 5 ≤ bytes.length)
    (htag : bytes.head? = some tag)
    (hfield : (bytes.drop 1).take 4 = AspisR1.PublicInitFrame.lengthBytes size) :
    bytes.take 5 = AspisR1.RecordFrameCodec.header tag size := by
  cases bytes with
  | nil => simp at hlen
  | cons b rest =>
      have hb : b = tag := by simpa using htag
      subst b
      have hrest : 4 ≤ rest.length := by simp at hlen; omega
      have hfield' : rest.take 4 = AspisR1.PublicInitFrame.lengthBytes size := by
        simpa using hfield
      simp [AspisR1.RecordFrameCodec.header, hfield']

theorem rustParse_eq_recordFrame_parse (tag : AspisV8R19.DuplexFrames.Byte) (size : Nat)
    (bytes : Bytes) (hsize : size < 2^32) :
    rustParse tag size bytes = AspisR1.RecordFrameCodec.parse tag size bytes := by
  by_cases htotal : bytes.length = 5 + size
  · have hlen5 : 5 ≤ bytes.length := by omega
    have hfieldlen : ((bytes.drop 1).take 4).length = 4 := by
      simp [List.length_take, List.length_drop]
      omega
    let words : WordBytes := fun i => ((bytes.drop 1).take 4).get ⟨i, by rw [hfieldlen]; omega⟩
    have hfixed : fixedBytes? 4 ((bytes.drop 1).take 4) = some words := by
      simp [fixedBytes?, words, hfieldlen]
    have hcheck : (bytes.head? = some tag ∧ (decodeWordLE words).val = size) ↔
        bytes.take 5 = AspisR1.RecordFrameCodec.header tag size := by
      constructor
      · rintro ⟨htag, hval⟩
        have hfield : (bytes.drop 1).take 4 = AspisR1.PublicInitFrame.lengthBytes size := by
          calc
            (bytes.drop 1).take 4 = List.ofFn words := (fixedBytes?_toList hfixed).symm
            _ = AspisR1.PublicInitFrame.lengthBytes size :=
              (decodeWordLE_val_eq_iff words size hsize).1 hval
        exact drop_take_header tag size bytes hlen5 htag hfield
      · intro hheader
        have htag : bytes.head? = some tag := by
          cases bytes with
          | nil => simp at hlen5
          | cons b rest =>
              have hb : b = tag := by
                have hfirst := congrArg List.head? hheader
                simpa [AspisR1.RecordFrameCodec.header] using hfirst
              simp [hb]
        have hfield : (bytes.drop 1).take 4 = AspisR1.PublicInitFrame.lengthBytes size := by
          cases bytes with
          | nil => simp at hlen5
          | cons b rest =>
              have hrest : 4 ≤ rest.length := by simp at hlen5; omega
              have htake := congrArg List.tail hheader
              have htail : (List.take 5 (b :: rest)).tail = List.take 4 rest := by
                simp [List.take_cons, hrest]
              have hrestfield : List.take 4 rest = AspisR1.PublicInitFrame.lengthBytes size := by
                simpa [AspisR1.RecordFrameCodec.header, htail] using htake
              simpa using hrestfield
        constructor
        · exact htag
        · have hwordList : List.ofFn words = AspisR1.PublicInitFrame.lengthBytes size := by
            calc
              List.ofFn words = (bytes.drop 1).take 4 := fixedBytes?_toList hfixed
              _ = AspisR1.PublicInitFrame.lengthBytes size := hfield
          exact (decodeWordLE_val_eq_iff words size hsize).2 hwordList
    unfold rustParse AspisR1.RecordFrameCodec.parse
    simp only [if_pos htotal, hfixed, Option.bind_some]
    by_cases htag : bytes.head? = some tag
    · by_cases hval : (decodeWordLE words).val = size
      · have hheader := hcheck.mp ⟨htag, hval⟩
        simp [htag, hval, hheader, htotal]
      · have hnotheader : bytes.take 5 ≠ AspisR1.RecordFrameCodec.header tag size := by
          intro hh
          exact hval ((hcheck.mpr hh).2)
        simp [htag, hval, hnotheader, htotal]
    · have hnotheader : bytes.take 5 ≠ AspisR1.RecordFrameCodec.header tag size := by
        intro hh
        exact htag (hcheck.mpr hh).1
      simp [htag, hnotheader, htotal]
  · simp [rustParse, AspisR1.RecordFrameCodec.parse, htotal]

#print axioms lengthBytes_eq_encodeWordLE
#print axioms decodeWordLE_val_eq_iff
#print axioms rustParse_eq_recordFrame_parse

end AspisR1.RecordLengthCodec
end
