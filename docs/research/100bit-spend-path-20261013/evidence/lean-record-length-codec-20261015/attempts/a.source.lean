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
  apply List.ofFn_injective
  funext j
  fin_cases j <;> apply Fin.ext <;>
    simp [AspisR1.PublicInitFrame.lengthBytes, encodeWordLE, byteMod,
      rawWordCount]

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
    have hbytes : bytes = encodeWordLE word := henc.symm
    have hlist : List.ofFn bytes = List.ofFn (encodeWordLE word) :=
      congrArg List.ofFn hbytes
    rw [lengthBytes_eq_encodeWordLE n hn]
    exact hlist
  · intro h
    have hbytes : bytes = encodeWordLE word :=
      List.ofFn_injective (by
        rw [h, lengthBytes_eq_encodeWordLE n hn])
    rw [hbytes, decodeWordLE_encodeWordLE]
    rfl

/-- Rust-style mathematical framing check: total size, tag byte, and a
four-byte little-endian decoded size. -/
def rustParse (tag : Byte) (size : Nat) (bytes : Bytes) : Option Bytes :=
  if bytes.length = 5 + size ∧ bytes.head? = some tag then
    (fixedBytes? 4 (bytes.drop 1 |>.take 4)).bind fun wordBytes =>
      if (decodeWordLE wordBytes).val = size then some (bytes.drop 5) else none
  else none

private theorem fixedBytes?_toList {xs : List Byte} {wordBytes : WordBytes}
    (h : fixedBytes? 4 xs = some wordBytes) : List.ofFn wordBytes = xs := by
  unfold fixedBytes? at h
  split at h
  · rename_i hlen
    injection h with hfun
    subst wordBytes
    apply List.ext_getElem
    · simp [List.length_ofFn, hlen]
    · intro i hi1 hi2
      simp [List.getElem_ofFn, hfun]
  · simp at h

theorem rustParse_eq_recordFrame_parse (tag : Byte) (size : Nat)
    (bytes : Bytes) (hsize : size < 2^32) :
    rustParse tag size bytes = AspisR1.RecordFrameCodec.parse tag size bytes := by
  by_cases htotal : bytes.length = 5 + size
  · have hlen5 : 5 ≤ bytes.length := by omega
    by_cases hheader : bytes.take 5 = AspisR1.RecordFrameCodec.header tag size
    · have htag : bytes.head? = some tag := by
        have hfirst := congrArg List.head? hheader
        simpa [AspisR1.RecordFrameCodec.header] using hfirst
      have hfield : bytes.drop 1 |>.take 4 =
          AspisR1.PublicInitFrame.lengthBytes size := by
        have hdrop := congrArg (fun xs : List Byte => xs.drop 1 |>.take 4) hheader
        simpa [AspisR1.RecordFrameCodec.header] using hdrop
      have hfixed : fixedBytes? 4 (bytes.drop 1 |>.take 4) =
          some (fun i => (AspisR1.PublicInitFrame.lengthBytes size).get
            ⟨i, by have := AspisR1.PublicInitFrame.lengthBytes_length size; omega⟩) := by
        simp [fixedBytes?, AspisR1.PublicInitFrame.lengthBytes_length, hfield]
      have hwordval : (decodeWordLE ((fixedBytes? 4 (bytes.drop 1 |>.take 4)).getD 0)).val = size := by
        rw [hfixed]
        have hbytesEq := (decodeWordLE_val_eq_iff _ size hsize).2
        apply hbytesEq
        simp [fixedBytes?]
      simp [rustParse, htotal, htag, hfixed, hwordval,
        AspisR1.RecordFrameCodec.parse, hheader]
    · have hnotrust : rustParse tag size bytes = none := by
        unfold rustParse
        simp [htotal]
        by_cases htag : bytes.head? = some tag
        · simp [htag]
          cases hfixed : fixedBytes? 4 (bytes.drop 1 |>.take 4) with
          | none => rfl
          | some wordBytes =>
              simp only [Option.bind_some]
              by_cases hv : (decodeWordLE wordBytes).val = size
              · exfalso
                have hfield := fixedBytes?_toList hfixed
                have hlenfield := congrArg List.length hfield
                have hfour : (bytes.drop 1 |>.take 4).length = 4 := by
                  simp [List.length_take, List.length_drop]
                  omega
                have hencoded := (decodeWordLE_val_eq_iff wordBytes size hsize).1 hv
                rw [hfield] at hencoded
                have hhead : bytes.take 5 = tag :: AspisR1.PublicInitFrame.lengthBytes size := by
                  cases bytes with
                  | nil => simp at htotal
                  | cons b rest =>
                    have hb : b = tag := by simpa using htag
                    subst b
                    have hrest : 4 ≤ rest.length := by simp at htotal; omega
                    simp [hencoded, List.take_cons, hrest]
                exact hheader (by simpa [AspisR1.RecordFrameCodec.header] using hhead)
              · simp [hv]
        · simp [htag]
      simp [AspisR1.RecordFrameCodec.parse, htotal, hheader, hnotrust]
  · simp [rustParse, AspisR1.RecordFrameCodec.parse, htotal]

#print axioms lengthBytes_eq_encodeWordLE
#print axioms decodeWordLE_val_eq_iff
#print axioms rustParse_eq_recordFrame_parse

end AspisR1.RecordLengthCodec
end
