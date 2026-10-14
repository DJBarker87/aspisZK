import AspisFormal.V5MerkleConsumedValueBridge
import AspisFormal.K1.V7Tag73SemanticTranscriptBridge

/-! List wrappers for the existing fixed-width field byte codecs. -/
set_option autoImplicit false

namespace AspisR1.ListFieldCodec

open AspisV5MerkleConsumedValueBridge
open AspisV5ComponentCQM31Representation
open AspisK1.V7Tag73SemanticTranscriptBridge

theorem fixedBytes?_ofFn (n : Nat) (f : Fin n → Byte) :
    fixedBytes? n (List.ofFn f) = some f := by
  simp [fixedBytes?, List.length_ofFn]

theorem fixedBytes?_sound (n : Nat) (xs : List Byte) (f : Fin n → Byte)
    (h : fixedBytes? n xs = some f) : List.ofFn f = xs := by
  unfold fixedBytes? at h
  split at h
  · rename_i hlen
    have hfun : (fun i : Fin n => xs.get ⟨i.val, by omega⟩) = f :=
      Option.some.inj h
    subst n
    simpa using (List.ofFn_get xs).trans (congrArg List.ofFn hfun.symm)
  · simp_all

def encodeM31Bytes (value : M31Value) : List Byte :=
  List.ofFn (encodeM31LE value)

def encodeQM31Bytes (limbs : QM31Limbs) : List Byte :=
  List.ofFn (encodeQM31LE limbs)

private theorem encodeM31LE_of_decodeM31LE
    (bytes : WordBytes) (value : M31Value)
    (h : decodeM31LE bytes = some value) : encodeM31LE value = bytes := by
  unfold decodeM31LE at h
  split at h
  · rename_i hcanonical
    have hv : (⟨decodeWordLE bytes, hcanonical⟩ : M31Value) = value :=
      Option.some.inj h
    subst value
    have hraw : m31AsRawWord ⟨decodeWordLE bytes, hcanonical⟩ = decodeWordLE bytes := by
      apply Fin.ext
      rfl
    rw [encodeM31LE, hraw, encodeWordLE_decodeWordLE]
  · simp_all

theorem decodeM31Bytes_encode (value : M31Value) :
    decodeM31Bytes (encodeM31Bytes value) = some value := by
  simp [decodeM31Bytes, encodeM31Bytes, fixedBytes?_ofFn,
    decodeM31LE_encodeM31LE]

theorem encodeM31Bytes_of_decode (bytes : List Byte) (value : M31Value)
    (h : decodeM31Bytes bytes = some value) :
    encodeM31Bytes value = bytes := by
  unfold decodeM31Bytes at h
  cases hf : fixedBytes? 4 bytes with
  | none => simp [hf] at h
  | some wordBytes =>
      have hdecode : decodeM31LE wordBytes = some value := by
        simpa [hf] using h
      rw [← encodeM31LE_of_decodeM31LE wordBytes value hdecode]
      exact fixedBytes?_sound 4 bytes wordBytes hf

theorem decodeQM31Bytes_encode (limbs : QM31Limbs) :
    decodeQM31Bytes (encodeQM31Bytes limbs) = some limbs := by
  simp [decodeQM31Bytes, encodeQM31Bytes, fixedBytes?_ofFn,
    decodeQM31LE_encodeQM31LE]

theorem encodeQM31Bytes_of_decode (bytes : List Byte) (limbs : QM31Limbs)
    (h : decodeQM31Bytes bytes = some limbs) :
    encodeQM31Bytes limbs = bytes := by
  unfold decodeQM31Bytes at h
  cases hf : fixedBytes? 16 bytes with
  | none => simp [hf] at h
  | some qmBytes =>
      have hdecode : decodeQM31LE qmBytes = some limbs := by
        simpa [hf] using h
      rw [← encodeQM31LE_of_decodeQM31LE qmBytes limbs hdecode]
      exact fixedBytes?_sound 16 bytes qmBytes hf

#print axioms fixedBytes?_ofFn
#print axioms fixedBytes?_sound
#print axioms decodeM31Bytes_encode
#print axioms encodeM31Bytes_of_decode
#print axioms decodeQM31Bytes_encode
#print axioms encodeQM31Bytes_of_decode

end AspisR1.ListFieldCodec
