import Mathlib.Tactic

/-! Verbatim retained byte and field codec declarations. Their source pins and the only permitted namespace qualification replacement are checked by tools/retain-field-byte-codec.py. This is a retained model interface, not a new source correspondence proof. -/
set_option autoImplicit false

namespace AspisR1.RetainedFieldByteCodec

abbrev rawCandidateCount : Nat := 2 ^ 31
abbrev rawWordCount : Nat := 2 ^ 32
abbrev m31Modulus : Nat := rawCandidateCount - 1
abbrev RawWord := Fin rawWordCount
abbrev M31Value := Fin m31Modulus
abbrev qm31LimbCount : Nat := 4
abbrev QM31Limbs := Fin qm31LimbCount → M31Value

abbrev Byte := Fin 256
abbrev WordBytes := Fin 4 → Byte
abbrev QM31Bytes := Fin 16 → Byte

private def byteMod (n : Nat) : Byte :=
  ⟨n % 256, Nat.mod_lt _ (by norm_num)⟩

/-- Four little-endian bytes of one mathematical `u32`. -/
def encodeWordLE (word : RawWord) : WordBytes :=
  ![byteMod word,
    byteMod ((word : Nat) / 256),
    byteMod ((word : Nat) / 65536),
    byteMod ((word : Nat) / 16777216)]

/-- Reassemble four little-endian bytes into one mathematical `u32`. -/
def decodeWordLE (bytes : WordBytes) : RawWord :=
  ⟨(bytes 0 : Nat) + 256 * (bytes 1 : Nat) +
      65536 * (bytes 2 : Nat) + 16777216 * (bytes 3 : Nat), by
    have h0 := (bytes 0).isLt
    have h1 := (bytes 1).isLt
    have h2 := (bytes 2).isLt
    have h3 := (bytes 3).isLt
    norm_num [rawWordCount] at *
    omega⟩

/-- The mathematical `u32` little-endian codec round trips exactly. -/
theorem decodeWordLE_encodeWordLE (word : RawWord) :
    decodeWordLE (encodeWordLE word) = word := by
  apply Fin.ext
  simp only [decodeWordLE, encodeWordLE, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Fin.val_mk, byteMod]
  have hword := word.isLt
  norm_num [rawWordCount] at hword ⊢
  omega

/-- Canonically embed one accepted M31 residue in a mathematical `u32`. -/
def m31AsRawWord (value : M31Value) : RawWord :=
  ⟨value, lt_trans value.isLt (by
    norm_num [m31Modulus, rawCandidateCount, rawWordCount])⟩

def encodeM31LE (value : M31Value) : WordBytes :=
  encodeWordLE (m31AsRawWord value)

/-- Canonical Rust-style M31 decoder: reject a `u32` at or above `P`. -/
def decodeM31LE (bytes : WordBytes) : Option M31Value :=
  let word := decodeWordLE bytes
  if h : (word : Nat) < m31Modulus then some ⟨word, h⟩ else none

theorem decodeM31LE_encodeM31LE (value : M31Value) :
    decodeM31LE (encodeM31LE value) = some value := by
  have hround : decodeWordLE (encodeM31LE value) = m31AsRawWord value :=
    decodeWordLE_encodeWordLE _
  have hlt : ((decodeWordLE (encodeM31LE value) : RawWord) : Nat) < m31Modulus := by
    rw [hround]
    exact value.isLt
  unfold decodeM31LE
  rw [dif_pos hlt]
  apply congrArg some
  apply Fin.ext
  calc
    ((decodeWordLE (encodeM31LE value) : RawWord) : Nat) =
        (m31AsRawWord value : Nat) := congrArg Fin.val hround
    _ = (value : Nat) := rfl

/-- Byte offset `byte + 4*limb`.  Thus limbs `0,1,2,3` occupy byte ranges
`0..4`, `4..8`, `8..12`, `12..16`, exactly Rust's
`(c0.a,c0.b,c1.a,c1.b)` order. -/
def limbByteIndex (limb byte : Fin 4) : Fin 16 :=
  finProdFinEquiv (limb, byte)

@[simp] theorem limbByteIndex_val (limb byte : Fin 4) :
    (limbByteIndex limb byte : Nat) = (byte : Nat) + 4 * (limb : Nat) := rfl

/-- Encode four limbs consecutively in the pinned tower order. -/
def encodeQM31LE (limbs : QM31Limbs) : QM31Bytes :=
  fun offset =>
    let position : Fin 4 × Fin 4 := finProdFinEquiv.symm offset
    encodeM31LE (limbs position.1) position.2

/-- Extract the four bytes belonging to one pinned limb. -/
def qm31LimbBytes (bytes : QM31Bytes) (limb : Fin 4) : WordBytes :=
  fun byte => bytes (limbByteIndex limb byte)

@[simp] theorem qm31LimbBytes_encodeQM31LE (limbs : QM31Limbs) (limb : Fin 4) :
    qm31LimbBytes (encodeQM31LE limbs) limb = encodeM31LE (limbs limb) := by
  funext byte
  simp [qm31LimbBytes, encodeQM31LE, limbByteIndex]

/-- Decode four consecutive canonical M31 words.  Any noncanonical limb is
rejected, just as `QM31::from_le_bytes` rejects through its nested M31
decoders. -/
def decodeQM31LE (bytes : QM31Bytes) : Option QM31Limbs :=
  if h : ∀ limb, ((decodeWordLE (qm31LimbBytes bytes limb) : RawWord) : Nat) <
      m31Modulus then
    some (fun limb => ⟨decodeWordLE (qm31LimbBytes bytes limb), h limb⟩)
  else none

/-- The exact `(c0.a,c0.b,c1.a,c1.b)` 16-byte codec round trip. -/
theorem decodeQM31LE_encodeQM31LE (limbs : QM31Limbs) :
    decodeQM31LE (encodeQM31LE limbs) = some limbs := by
  have hword (limb : Fin 4) :
      decodeWordLE (qm31LimbBytes (encodeQM31LE limbs) limb) =
        m31AsRawWord (limbs limb) := by
    rw [qm31LimbBytes_encodeQM31LE]
    exact decodeWordLE_encodeWordLE _
  have hlt : ∀ limb,
      ((decodeWordLE (qm31LimbBytes (encodeQM31LE limbs) limb) : RawWord) : Nat) <
        m31Modulus := by
    intro limb
    rw [hword]
    exact (limbs limb).isLt
  unfold decodeQM31LE
  rw [dif_pos hlt]
  apply congrArg some
  funext limb
  apply Fin.ext
  calc
    ((decodeWordLE (qm31LimbBytes (encodeQM31LE limbs) limb) : RawWord) : Nat) =
        (m31AsRawWord (limbs limb) : Nat) := congrArg Fin.val (hword limb)
    _ = (limbs limb : Nat) := rfl

theorem encodeWordLE_decodeWordLE (wordBytes : WordBytes) :
    encodeWordLE (decodeWordLE wordBytes) = wordBytes := by
  have injective : Function.Injective encodeWordLE :=
    Function.LeftInverse.injective decodeWordLE_encodeWordLE
  have sameCard : Fintype.card RawWord = Fintype.card WordBytes := by
    simp [RawWord, WordBytes, rawWordCount]
  have surjective : Function.Surjective encodeWordLE :=
    ((Fintype.bijective_iff_injective_and_card encodeWordLE).2
      ⟨injective, sameCard⟩).2
  obtain ⟨word, encoded⟩ := surjective wordBytes
  rw [← encoded, decodeWordLE_encodeWordLE]

/-- Successful canonical four-limb decoding determines every input byte. -/

theorem encodeQM31LE_of_decodeQM31LE
    (encoded : AspisR1.RetainedFieldByteCodec.QM31Bytes)
    (limbs : QM31Limbs) (decoded : decodeQM31LE encoded = some limbs) :
    encodeQM31LE limbs = encoded := by
  unfold decodeQM31LE at decoded
  split at decoded
  next canonical =>
    have limbsEq := Option.some.inj decoded
    rw [← limbsEq]
    funext offset
    let position : Fin 4 × Fin 4 := finProdFinEquiv.symm offset
    have rawEq :
        m31AsRawWord
            ⟨decodeWordLE (qm31LimbBytes encoded position.1),
              canonical position.1⟩ =
          decodeWordLE (qm31LimbBytes encoded position.1) := by
      apply Fin.ext
      rfl
    change encodeM31LE
        ⟨decodeWordLE (qm31LimbBytes encoded position.1),
          canonical position.1⟩ position.2 = encoded offset
    rw [encodeM31LE, rawEq, encodeWordLE_decodeWordLE]
    change encoded (limbByteIndex position.1 position.2) = encoded offset
    congr 1
    exact (finProdFinEquiv (m := 4) (n := 4)).apply_symm_apply offset
  next noncanonical => simp at decoded

/-- A successful Tag-73 canonical decode round-trips to the literal runtime
bytes, not merely to an extension-field value with the same cardinality. -/

def fixedBytes? (width : Nat) (bytes : List Byte) :
    Option (Fin width -> Byte) :=
  if h : bytes.length = width then
    some fun index => bytes.get ⟨index, by omega⟩
  else none

def byteSlice (bytes : List Byte) (offset width : Nat) : List Byte :=
  (bytes.drop offset).take width

def decodeM31Bytes (bytes : List Byte) :=
  (fixedBytes? 4 bytes).bind
    AspisR1.RetainedFieldByteCodec.decodeM31LE

def decodeQM31Bytes (bytes : List Byte) :=
  (fixedBytes? 16 bytes).bind
    AspisR1.RetainedFieldByteCodec.decodeQM31LE

#print axioms decodeWordLE_encodeWordLE

#print axioms decodeM31LE_encodeM31LE

#print axioms decodeQM31LE_encodeQM31LE

#print axioms encodeWordLE_decodeWordLE

#print axioms encodeQM31LE_of_decodeQM31LE

#print axioms decodeQM31Bytes

end AspisR1.RetainedFieldByteCodec
