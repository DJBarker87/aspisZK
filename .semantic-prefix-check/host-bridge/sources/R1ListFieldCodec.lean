import R1RetainedFieldByteCodec

/-! List wrappers for the existing fixed-width field byte codecs. -/
set_option autoImplicit false

namespace AspisR1.ListFieldCodec

open AspisR1.RetainedFieldByteCodec

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
    have hf : f = xs.get := by
      funext i
      exact (congrFun hfun i).symm
    rw [hf]
    exact List.ofFn_get xs
  · simp_all

def encodeM31Bytes (value : M31Value) : List Byte :=
  List.ofFn (encodeM31LE value)

def encodeQM31Bytes (limbs : QM31Limbs) : List Byte :=
  List.ofFn (encodeQM31LE limbs)

private theorem encodeM31LE_of_decodeM31LE
    (bytes : WordBytes) (value : M31Value)
    (h : decodeM31LE bytes = some value) : encodeM31LE value = bytes := by
  simp only [decodeM31LE] at h
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
  change (fixedBytes? 4 (List.ofFn (encodeM31LE value))).bind decodeM31LE = _
  rw [fixedBytes?_ofFn]
  exact decodeM31LE_encodeM31LE value

theorem encodeM31Bytes_of_decode (bytes : List Byte) (value : M31Value)
    (h : decodeM31Bytes bytes = some value) :
    encodeM31Bytes value = bytes := by
  unfold decodeM31Bytes at h
  cases hf : fixedBytes? 4 bytes with
  | none => simp [hf] at h
  | some wordBytes =>
      have hdecode : decodeM31LE wordBytes = some value := by
        simpa [hf] using h
      change List.ofFn (encodeM31LE value) = bytes
      rw [encodeM31LE_of_decodeM31LE wordBytes value hdecode]
      exact fixedBytes?_sound 4 bytes wordBytes hf

theorem decodeQM31Bytes_encode (limbs : QM31Limbs) :
    decodeQM31Bytes (encodeQM31Bytes limbs) = some limbs := by
  change (fixedBytes? 16 (List.ofFn (encodeQM31LE limbs))).bind decodeQM31LE = _
  rw [fixedBytes?_ofFn]
  exact decodeQM31LE_encodeQM31LE limbs

theorem encodeQM31Bytes_of_decode (bytes : List Byte) (limbs : QM31Limbs)
    (h : decodeQM31Bytes bytes = some limbs) :
    encodeQM31Bytes limbs = bytes := by
  unfold decodeQM31Bytes at h
  cases hf : fixedBytes? 16 bytes with
  | none => simp [hf] at h
  | some qmBytes =>
      have hdecode : decodeQM31LE qmBytes = some limbs := by
        simpa [hf] using h
      change List.ofFn (encodeQM31LE limbs) = bytes
      rw [encodeQM31LE_of_decodeQM31LE qmBytes limbs hdecode]
      exact fixedBytes?_sound 16 bytes qmBytes hf

#print axioms fixedBytes?_ofFn
#print axioms fixedBytes?_sound
#print axioms decodeM31Bytes_encode
#print axioms encodeM31Bytes_of_decode
#print axioms decodeQM31Bytes_encode
#print axioms encodeQM31Bytes_of_decode

end AspisR1.ListFieldCodec
