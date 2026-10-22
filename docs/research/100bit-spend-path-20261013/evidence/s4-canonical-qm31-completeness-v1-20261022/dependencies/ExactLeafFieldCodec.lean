import R1ListFieldCodec
import R1RetainedFieldByteCodec
import R1RetainedExactLimbCodec

/-! Exact-tower wrappers around the existing V5 list-backed M31/QM31 codecs.
This file composes mathematical codec identities only; it states no current
Rust parser or R1 source correspondence. -/
set_option autoImplicit false

namespace AspisR1.ExactLeafFieldCodec

open AspisR1.RetainedFieldByteCodec
open AspisR1.RetainedExactLimbCodec

abbrev Byte := AspisR1.RetainedFieldByteCodec.Byte
abbrev M31Exact := AspisV8R15.ExactTowerBase.M31Exact
abbrev QM31Exact := AspisV8R15.ExactTowerBase.QM31Exact

/-- Four-byte little-endian encoding of one exact M31 element. -/
def encodeM31 (x : M31Exact) : List Byte :=
  AspisR1.ListFieldCodec.encodeM31Bytes (m31ResidueEquiv.symm x)

/-- Strict exact-length, canonical decoder for one M31 element. -/
def decodeM31 (bytes : List Byte) : Option M31Exact :=
  (AspisR1.RetainedFieldByteCodec.decodeM31Bytes bytes).map m31ResidueEquiv

/-- Sixteen-byte little-endian encoding in `(c0.a,c0.b,c1.a,c1.b)` order. -/
def encodeQM31 (x : QM31Exact) : List Byte :=
  AspisR1.ListFieldCodec.encodeQM31Bytes (qm31ExactLimbEquiv.symm x)

/-- Strict exact-length, canonical decoder into the exact QM31 tower. -/
def decodeQM31 (bytes : List Byte) : Option QM31Exact :=
  (AspisR1.RetainedFieldByteCodec.decodeQM31Bytes bytes).map qm31ExactLimbEquiv

theorem encodeM31_length (x : M31Exact) : (encodeM31 x).length = 4 := by
  simp [encodeM31, AspisR1.ListFieldCodec.encodeM31Bytes]

theorem decodeM31_encodeM31 (x : M31Exact) : decodeM31 (encodeM31 x) = some x := by
  simp [decodeM31, encodeM31, AspisR1.ListFieldCodec.decodeM31Bytes_encode]

theorem encodeM31_of_decodeM31 (bytes : List Byte) (x : M31Exact)
    (h : decodeM31 bytes = some x) : encodeM31 x = bytes := by
  unfold decodeM31 at h
  cases hd : AspisR1.RetainedFieldByteCodec.decodeM31Bytes bytes with
  | none => simp [hd] at h
  | some value =>
      simp only [hd, Option.map_some] at h
      have hv : value = m31ResidueEquiv.symm x := by
        calc
          value = m31ResidueEquiv.symm (m31ResidueEquiv value) :=
            (m31ResidueEquiv.symm_apply_apply value).symm
          _ = m31ResidueEquiv.symm x := congrArg m31ResidueEquiv.symm (Option.some.inj h)
      change AspisR1.ListFieldCodec.encodeM31Bytes (m31ResidueEquiv.symm x) = bytes
      rw [← hv]
      exact AspisR1.ListFieldCodec.encodeM31Bytes_of_decode bytes value hd

theorem encodeM31_injective : Function.Injective encodeM31 := by
  intro x y hxy
  have hsome : some x = some y := by
    calc
      some x = decodeM31 (encodeM31 x) := (decodeM31_encodeM31 x).symm
      _ = decodeM31 (encodeM31 y) := congrArg decodeM31 hxy
      _ = some y := decodeM31_encodeM31 y
  exact Option.some.inj hsome

theorem encodeQM31_length (x : QM31Exact) : (encodeQM31 x).length = 16 := by
  simp [encodeQM31, AspisR1.ListFieldCodec.encodeQM31Bytes]

theorem decodeQM31_encodeQM31 (x : QM31Exact) : decodeQM31 (encodeQM31 x) = some x := by
  simp [decodeQM31, encodeQM31, AspisR1.ListFieldCodec.decodeQM31Bytes_encode]

theorem encodeQM31_of_decodeQM31 (bytes : List Byte) (x : QM31Exact)
    (h : decodeQM31 bytes = some x) : encodeQM31 x = bytes := by
  unfold decodeQM31 at h
  cases hd : AspisR1.RetainedFieldByteCodec.decodeQM31Bytes bytes with
  | none => simp [hd] at h
  | some value =>
      simp only [hd, Option.map_some] at h
      have hv : value = qm31ExactLimbEquiv.symm x := by
        calc
          value = qm31ExactLimbEquiv.symm (qm31ExactLimbEquiv value) :=
            (qm31ExactLimbEquiv.symm_apply_apply value).symm
          _ = qm31ExactLimbEquiv.symm x := congrArg qm31ExactLimbEquiv.symm (Option.some.inj h)
      change AspisR1.ListFieldCodec.encodeQM31Bytes (qm31ExactLimbEquiv.symm x) = bytes
      rw [← hv]
      exact AspisR1.ListFieldCodec.encodeQM31Bytes_of_decode bytes value hd

theorem encodeQM31_injective : Function.Injective encodeQM31 := by
  intro x y hxy
  have hsome : some x = some y := by
    calc
      some x = decodeQM31 (encodeQM31 x) := (decodeQM31_encodeQM31 x).symm
      _ = decodeQM31 (encodeQM31 y) := congrArg decodeQM31 hxy
      _ = some y := decodeQM31_encodeQM31 y
  exact Option.some.inj hsome

#print axioms encodeM31_length
#print axioms decodeM31_encodeM31
#print axioms encodeM31_of_decodeM31
#print axioms encodeM31_injective
#print axioms encodeQM31_length
#print axioms decodeQM31_encodeQM31
#print axioms encodeQM31_of_decodeQM31
#print axioms encodeQM31_injective

end AspisR1.ExactLeafFieldCodec
