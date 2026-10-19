import R1RetainedFieldByteCodec

/-! A mathematical little-endian codec for a 64-bit public index, assembled
from the retained 32-bit word codec. This is a representation lemma only; it
does not establish a Rust extraction or caller-width correspondence. -/
set_option autoImplicit false

namespace AspisR1.PublicIndexCodec

open AspisR1.RetainedFieldByteCodec

abbrev Index := Fin (2 ^ 64)
abbrev IndexBytes := Fin 8 → Byte

private def lowWordBytes (bytes : IndexBytes) : WordBytes :=
  fun i => bytes ⟨i.val, by omega⟩

private def highWordBytes (bytes : IndexBytes) : WordBytes :=
  fun i => bytes ⟨i.val + 4, by omega⟩

private def lowWord (x : Index) : RawWord :=
  ⟨x.val % 2 ^ 32, by
    exact Nat.mod_lt _ (by norm_num)⟩

private def highWord (x : Index) : RawWord :=
  ⟨x.val / 2 ^ 32, by
    have hx := x.isLt
    norm_num at hx ⊢
    omega⟩

/-- Eight little-endian bytes, with the low word followed by the high word. -/
def encode (x : Index) : IndexBytes := fun i =>
  if h : i.val < 4 then
    encodeWordLE (lowWord x) ⟨i.val, h⟩
  else
    encodeWordLE (highWord x) ⟨i.val - 4, by omega⟩

/-- Interpret eight little-endian bytes as a bounded 64-bit index. -/
def decode (bytes : IndexBytes) : Index :=
  ⟨(decodeWordLE (lowWordBytes bytes)).val +
      2 ^ 32 * (decodeWordLE (highWordBytes bytes)).val, by
    have hlo := (decodeWordLE (lowWordBytes bytes)).isLt
    have hhi := (decodeWordLE (highWordBytes bytes)).isLt
    norm_num [rawWordCount] at hlo hhi ⊢
    omega⟩

theorem decode_val (bytes : IndexBytes) :
    (decode bytes).val = (decodeWordLE (lowWordBytes bytes)).val +
      2 ^ 32 * (decodeWordLE (highWordBytes bytes)).val := rfl

theorem decode_encode (x : Index) : decode (encode x) = x := by
  apply Fin.ext
  rw [decode_val]
  have hlow : lowWordBytes (encode x) = encodeWordLE (lowWord x) := by
    funext i
    simp [lowWordBytes, encode, i.isLt]
  have hhigh : highWordBytes (encode x) = encodeWordLE (highWord x) := by
    funext i
    simp [highWordBytes, encode]
  rw [hlow, hhigh, decodeWordLE_encodeWordLE, decodeWordLE_encodeWordLE]
  change x.val % 2 ^ 32 + 2 ^ 32 * (x.val / 2 ^ 32) = x.val
  have hdiv := Nat.mod_add_div x.val (2 ^ 32)
  norm_num at hdiv
  exact hdiv

private theorem decode_lowWord (bytes : IndexBytes) :
    lowWord (decode bytes) = decodeWordLE (lowWordBytes bytes) := by
  apply Fin.ext
  change (decode bytes).val % 2 ^ 32 = (decodeWordLE (lowWordBytes bytes)).val
  rw [decode_val]
  have hlo := (decodeWordLE (lowWordBytes bytes)).isLt
  norm_num [rawWordCount] at hlo ⊢
  omega

private theorem decode_highWord (bytes : IndexBytes) :
    highWord (decode bytes) = decodeWordLE (highWordBytes bytes) := by
  apply Fin.ext
  change (decode bytes).val / 2 ^ 32 = (decodeWordLE (highWordBytes bytes)).val
  rw [decode_val]
  have hlo := (decodeWordLE (lowWordBytes bytes)).isLt
  have hhi := (decodeWordLE (highWordBytes bytes)).isLt
  norm_num [rawWordCount] at hlo hhi ⊢
  omega

theorem encode_decode (bytes : IndexBytes) : encode (decode bytes) = bytes := by
  funext i
  by_cases h : i.val < 4
  · simp only [encode, dif_pos h]
    rw [decode_lowWord]
    have hidx : (⟨i.val, h⟩ : Fin 4) = ⟨i.val, by omega⟩ := rfl
    rw [hidx]
    have hround := encodeWordLE_decodeWordLE (lowWordBytes bytes)
    exact congrArg (fun b : WordBytes => b ⟨i.val, by omega⟩) hround
  · simp only [encode, dif_neg h]
    rw [decode_highWord]
    have hround := encodeWordLE_decodeWordLE (highWordBytes bytes)
    have hbytes := congrArg (fun b : WordBytes => b ⟨i.val - 4, by omega⟩) hround
    change encodeWordLE (decodeWordLE (highWordBytes bytes)) ⟨i.val - 4, by omega⟩ =
      bytes ⟨i.val - 4 + 4, by omega⟩ at hbytes
    have hidx : (⟨i.val - 4 + 4, by omega⟩ : Fin 8) = i := by
      apply Fin.ext
      simp
      omega
    rw [hidx] at hbytes
    exact hbytes

end AspisR1.PublicIndexCodec

#print axioms AspisR1.PublicIndexCodec.decode_val
#print axioms AspisR1.PublicIndexCodec.decode_encode
#print axioms AspisR1.PublicIndexCodec.encode_decode
