import R1RetainedFieldByteCodec

/-! A strict byte-model codec for two consecutive 16-byte QM31 encodings.
This file reuses the existing strict QM31 decoder and does not claim source
parser correspondence or any arithmetic property of a wide field. -/
set_option autoImplicit false

namespace AspisR1.StrictWideByteCodec

open AspisR1.RetainedFieldByteCodec

abbrev WideBytes := Fin 32 → Byte
abbrev WideLimbs := QM31Limbs × QM31Limbs

def lowBytes (bytes : WideBytes) : QM31Bytes :=
  fun i => bytes (Fin.castAdd 16 i)

def highBytes (bytes : WideBytes) : QM31Bytes :=
  fun i => bytes (Fin.natAdd 16 i)

def encodeWideLE (limbs : WideLimbs) : WideBytes :=
  Fin.append (encodeQM31LE limbs.1) (encodeQM31LE limbs.2)

def decodeWideLE (bytes : WideBytes) : Option WideLimbs := do
  let lo ← decodeQM31LE (lowBytes bytes)
  let hi ← decodeQM31LE (highBytes bytes)
  some (lo, hi)

theorem decodeWideLE_encodeWideLE (limbs : WideLimbs) :
    decodeWideLE (encodeWideLE limbs) = some limbs := by
  rcases limbs with ⟨lo, hi⟩
  simp [decodeWideLE, lowBytes, highBytes, encodeWideLE,
    decodeQM31LE_encodeQM31LE]

theorem successful_halves (bytes : WideBytes) (limbs : WideLimbs)
    (h : decodeWideLE bytes = some limbs) :
    decodeQM31LE (lowBytes bytes) = some limbs.1 ∧
      decodeQM31LE (highBytes bytes) = some limbs.2 := by
  rcases limbs with ⟨lo, hi⟩
  unfold decodeWideLE at h
  cases hlo : decodeQM31LE (lowBytes bytes) <;>
    cases hhi : decodeQM31LE (highBytes bytes) <;>
    simp_all

theorem encodeWideLE_of_decodeWideLE (bytes : WideBytes) (limbs : WideLimbs)
    (h : decodeWideLE bytes = some limbs) :
    encodeWideLE limbs = bytes := by
  rcases limbs with ⟨lo, hi⟩
  obtain ⟨hlo, hhi⟩ := successful_halves bytes (lo, hi) h
  have hlo' := encodeQM31LE_of_decodeQM31LE (lowBytes bytes) lo hlo
  have hhi' := encodeQM31LE_of_decodeQM31LE (highBytes bytes) hi hhi
  funext i
  by_cases hlow : i.val < 16
  · let j : Fin 16 := ⟨i.val, hlow⟩
    have hi' : i = Fin.castAdd 16 j := Fin.ext rfl
    rw [hi']
    simpa [encodeWideLE, lowBytes] using congrFun hlo' j
  · let j : Fin 16 := ⟨i.val - 16, by omega⟩
    have hi' : i = Fin.natAdd 16 j := by
      apply Fin.ext
      simp only [Fin.natAdd, Fin.val_mk]
      omega
    rw [hi']
    simpa [encodeWideLE, highBytes] using congrFun hhi' j

#print axioms decodeWideLE_encodeWideLE
#print axioms encodeWideLE_of_decodeWideLE
#print axioms successful_halves

end AspisR1.StrictWideByteCodec
