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

#print axioms lengthBytes_eq_encodeWordLE
#print axioms decodeWordLE_val_eq_iff

end AspisR1.RecordLengthCodec
end
