import ExtractedPrefixFieldAgreement
import ExtractedRecordByteValue
import ExtractedRecordByteCanonicality
import R1StrictWideByteCodec

/-! Fixed eight-word codec agreement. The retained codec is unchanged; no
wide-field algebra, semantic record, or prefix theorem is assumed. -/
namespace AspisR1.ExtractedRecordStrictCodec
open Aeneas Aeneas.Std
open ExtractedRecordByteValue ExtractedRecordByteCanonicality
open RetainedFieldByteCodec StrictWideByteCodec

def arrayBytes (arr : Array U8 32#usize) : WideBytes :=
  fun i => rawByte (byteAt arr i)

/-- The fixed carrier contains exactly the input array bytes, in order. -/
theorem arrayBytes_list (arr : Array U8 32#usize) :
    List.ofFn (arrayBytes arr) = arr.val.map rawByte := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_map]
    exact arr.property.symm
  · intro i hi hj
    simp only [List.getElem_ofFn, List.getElem_map, arrayBytes, byteAt]

def wordBytesAt (arr : Array U8 32#usize) (i : Fin 8) : WordBytes :=
  fun j => rawByte (byteAt arr ⟨j.val + 4 * i.val, by omega⟩)

theorem decodeWord_at (arr : Array U8 32#usize) (i : Fin 8) :
    decodeWordLE (wordBytesAt arr i) = (wordLE arr i).bv.toFin := by
  have hbytes : wordBytesAt arr i =
      ![rawByte (byteAt arr ⟨4 * i.val, by omega⟩),
        rawByte (byteAt arr ⟨4 * i.val + 1, by omega⟩),
        rawByte (byteAt arr ⟨4 * i.val + 2, by omega⟩),
        rawByte (byteAt arr ⟨4 * i.val + 3, by omega⟩)] := by
    funext j
    fin_cases j <;> simp [wordBytesAt, Nat.add_comm]
  rw [hbytes, decodeWordLE_agreement]
  rfl

theorem low_wordBytes (arr : Array U8 32#usize) (i : Fin 4) :
    qm31LimbBytes (lowBytes (arrayBytes arr)) i =
      wordBytesAt arr (Fin.castAdd 4 i) := by rfl

theorem high_wordBytes (arr : Array U8 32#usize) (i : Fin 4) :
    qm31LimbBytes (highBytes (arrayBytes arr)) i =
      wordBytesAt arr (Fin.natAdd 4 i) := by
  funext j
  apply congrArg (fun index : Fin 32 => rawByte (byteAt arr index))
  apply Fin.ext
  change 16 + (j.val + 4 * i.val) = j.val + 4 * (4 + i.val)
  omega

def canonicalWords (arr : Array U8 32#usize)
    (h : ∀ i : Fin 8, (wordLE arr i).val < 2147483647) : Fin 8 → M31Value :=
  fun i => ⟨(wordLE arr i).val, h i⟩

def canonicalLimbs (arr : Array U8 32#usize)
    (h : ∀ i : Fin 8, (wordLE arr i).val < 2147483647) : WideLimbs :=
  (fun i => canonicalWords arr h (Fin.castAdd 4 i),
   fun i => canonicalWords arr h (Fin.natAdd 4 i))

theorem low_decode (arr : Array U8 32#usize)
    (h : ∀ i : Fin 8, (wordLE arr i).val < 2147483647) :
    decodeQM31LE (lowBytes (arrayBytes arr)) = some (canonicalLimbs arr h).1 := by
  have hc : ∀ i : Fin 4,
      (decodeWordLE (qm31LimbBytes (lowBytes (arrayBytes arr)) i)).val < m31Modulus := by
    intro i
    rw [low_wordBytes, decodeWord_at]
    exact h (Fin.castAdd 4 i)
  unfold decodeQM31LE
  rw [dif_pos hc]
  apply congrArg some
  funext i
  apply Fin.ext
  change (decodeWordLE (qm31LimbBytes (lowBytes (arrayBytes arr)) i)).val =
    (wordLE arr (Fin.castAdd 4 i)).val
  rw [low_wordBytes, decodeWord_at]
  rfl

theorem high_decode (arr : Array U8 32#usize)
    (h : ∀ i : Fin 8, (wordLE arr i).val < 2147483647) :
    decodeQM31LE (highBytes (arrayBytes arr)) = some (canonicalLimbs arr h).2 := by
  have hc : ∀ i : Fin 4,
      (decodeWordLE (qm31LimbBytes (highBytes (arrayBytes arr)) i)).val < m31Modulus := by
    intro i
    rw [high_wordBytes, decodeWord_at]
    exact h (Fin.natAdd 4 i)
  unfold decodeQM31LE
  rw [dif_pos hc]
  apply congrArg some
  funext i
  apply Fin.ext
  change (decodeWordLE (qm31LimbBytes (highBytes (arrayBytes arr)) i)).val =
    (wordLE arr (Fin.natAdd 4 i)).val
  rw [high_wordBytes, decodeWord_at]
  rfl

theorem strict_decode (arr : Array U8 32#usize)
    (h : ∀ i : Fin 8, (wordLE arr i).val < 2147483647) :
    decodeWideLE (arrayBytes arr) = some (canonicalLimbs arr h) := by
  simp only [decodeWideLE, low_decode arr h, high_decode arr h,
    Option.bind_some]
  rfl

/-- Actual final Prefix-E field decoding supplies canonicality and exact
input bytes for the unchanged strict codec, through the proved carrier map. -/
theorem actual_decode_strict (bytes : Slice U8)
    (w : AspisR1PrefixAggregateParser.field.wide_exact.WideExact)
    (h : AspisR1PrefixAggregateParser.field.wide_exact.WideExact.from_le_bytes bytes =
      Result.ok (some w)) :
    ∃ arr : Array U8 32#usize, arr.val = bytes.val ∧
      ∃ canonical : ∀ i : Fin 8, (wordLE arr i).val < 2147483647,
        decodeWideLE (arrayBytes arr) = some (canonicalLimbs arr canonical) ∧
        ExtractedPrefixFieldAgreement.wideToRecord w =
          ExtractedRecordLimbCanonicality.packed
            (wordLE arr 0) (wordLE arr 1) (wordLE arr 2) (wordLE arr 3)
            (wordLE arr 4) (wordLE arr 5) (wordLE arr 6) (wordLE arr 7) := by
  obtain ⟨_, arr, hbytes, hc, hp⟩ := slice_success bytes
    (ExtractedPrefixFieldAgreement.wideToRecord w)
    (ExtractedPrefixFieldAgreement.from_le_bytes_success bytes w h)
  refine ⟨arr, ?_, hc, strict_decode arr hc, hp⟩
  simpa only [Array.to_slice] using congrArg (fun s : Slice U8 => s.val) hbytes

end AspisR1.ExtractedRecordStrictCodec

#print axioms AspisR1.ExtractedRecordStrictCodec.arrayBytes_list
#print axioms AspisR1.ExtractedRecordStrictCodec.decodeWord_at
#print axioms AspisR1.ExtractedRecordStrictCodec.low_wordBytes
#print axioms AspisR1.ExtractedRecordStrictCodec.high_wordBytes
#print axioms AspisR1.ExtractedRecordStrictCodec.low_decode
#print axioms AspisR1.ExtractedRecordStrictCodec.high_decode
#print axioms AspisR1.ExtractedRecordStrictCodec.strict_decode

#print axioms AspisR1.ExtractedRecordStrictCodec.actual_decode_strict
