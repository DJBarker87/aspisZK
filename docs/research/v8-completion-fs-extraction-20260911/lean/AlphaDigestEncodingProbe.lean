import FSNonzeroQM31
import FSV7FourBlockWordBridge

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1200

namespace AspisV8Completion.AlphaDigestEncodingProbe

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSNonzeroQM31 FSV7OODSampler
open AspisV5ComponentCQM31TowerExact
open AspisV5ComponentCRejectionSampler
open AspisV5ComponentCQM31Representation
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73SamplerDecoder

noncomputable section

abbrev K := FSNonzeroQM31.K

def canonicalLimbs (value : K) : QM31Limbs :=
  qm31ExactToLimbs value

def canonicalLimbList (value : K) : List Nat :=
  [(canonicalLimbs value 0 : Nat), (canonicalLimbs value 1 : Nat),
    (canonicalLimbs value 2 : Nat), (canonicalLimbs value 3 : Nat)]

def canonicalOutput (value : K) : FSBoundedTranscript.Block := by
  let encoded := exactQm31BytesToTag (encodeQM31ExactLE value)
  exact fun i => if h : i.val < 16 then encoded ⟨i.val, h⟩ else 0

/- The algebraic half is available: four canonical limbs reconstruct the exact
   QM31 value.  This is independent of oracle execution. -/
theorem canonical_limbs_reconstruct (value : K) :
    limbsToQM31Exact (canonicalLimbs value) = value := by
  exact limbsToQM31Exact_qm31ExactToLimbs value

/- The sampler's `assemble` accepts the canonical four limbs. -/
theorem assemble_canonical_limbs (value : K) :
    assemble (canonicalLimbList value) = some value := by
  let limbs := canonicalLimbs value
  have bounded :
      (limbs 0 : Nat) < P ∧ (limbs 1 : Nat) < P ∧
        (limbs 2 : Nat) < P ∧ (limbs 3 : Nat) < P :=
    ⟨(limbs 0).isLt, (limbs 1).isLt, (limbs 2).isLt, (limbs 3).isLt⟩
  change assemble
    [(limbs 0 : Nat), (limbs 1 : Nat), (limbs 2 : Nat), (limbs 3 : Nat)] =
      some value
  simp only [assemble, dif_pos bounded]
  congr

theorem canonical_output_first_four_words (value : K) (index : Fin 4) :
    littleEndianWord (canonicalOutput value) ⟨index, by omega⟩ =
      (canonicalLimbs value index : Nat) := by
  fin_cases index
  · simp only [littleEndianWord, canonicalOutput, canonicalLimbs,
      exactQm31BytesToTag, encodeQM31ExactLE, tagByteEquivExactByte,
      Fin.val_zero, Nat.mul_zero, Fin.isValue, Nat.zero_mod, ↓reduceDIte,
      UInt8.toNat_ofFin, Equiv.symm_apply_apply]
    change ((decodeWordLE (qm31LimbBytes
      (encodeQM31LE (qm31ExactToLimbs value)) 0) : RawWord) : Nat) = _
    rw [qm31LimbBytes_encodeQM31LE]
    exact congrArg Fin.val (decodeWordLE_encodeWordLE
      (m31AsRawWord (qm31ExactToLimbs value 0)))
  · simp only [littleEndianWord, canonicalOutput, canonicalLimbs,
      exactQm31BytesToTag, encodeQM31ExactLE, tagByteEquivExactByte,
      Fin.isValue, ↓reduceDIte, UInt8.toNat_ofFin, Equiv.symm_apply_apply]
    change ((decodeWordLE (qm31LimbBytes
      (encodeQM31LE (qm31ExactToLimbs value)) 1) : RawWord) : Nat) = _
    rw [qm31LimbBytes_encodeQM31LE]
    exact congrArg Fin.val (decodeWordLE_encodeWordLE
      (m31AsRawWord (qm31ExactToLimbs value 1)))
  · simp only [littleEndianWord, canonicalOutput, canonicalLimbs,
      exactQm31BytesToTag, encodeQM31ExactLE, tagByteEquivExactByte,
      Fin.isValue, ↓reduceDIte, UInt8.toNat_ofFin, Equiv.symm_apply_apply]
    change ((decodeWordLE (qm31LimbBytes
      (encodeQM31LE (qm31ExactToLimbs value)) 2) : RawWord) : Nat) = _
    rw [qm31LimbBytes_encodeQM31LE]
    exact congrArg Fin.val (decodeWordLE_encodeWordLE
      (m31AsRawWord (qm31ExactToLimbs value 2)))
  · simp only [littleEndianWord, canonicalOutput, canonicalLimbs,
      exactQm31BytesToTag, encodeQM31ExactLE, tagByteEquivExactByte,
      Fin.isValue, ↓reduceDIte, UInt8.toNat_ofFin, Equiv.symm_apply_apply]
    change ((decodeWordLE (qm31LimbBytes
      (encodeQM31LE (qm31ExactToLimbs value)) 3) : RawWord) : Nat) = _
    rw [qm31LimbBytes_encodeQM31LE]
    exact congrArg Fin.val (decodeWordLE_encodeWordLE
      (m31AsRawWord (qm31ExactToLimbs value 3)))

theorem words_take_four_canonical_output (value : K) :
    (FSBoundedTranscript.words (canonicalOutput value)).take 4 =
      canonicalLimbList value := by
  rw [FSV7FourBlockWordBridge.current_words_eq_masked_blockWords]
  have h0 : littleEndianWord (canonicalOutput value) (0 : Fin 8) =
      (canonicalLimbs value 0 : Nat) := by
    simpa using canonical_output_first_four_words value (0 : Fin 4)
  have h1 : littleEndianWord (canonicalOutput value) (1 : Fin 8) =
      (canonicalLimbs value 1 : Nat) := by
    simpa using canonical_output_first_four_words value (1 : Fin 4)
  have h2 : littleEndianWord (canonicalOutput value) (2 : Fin 8) =
      (canonicalLimbs value 2 : Nat) := by
    simpa using canonical_output_first_four_words value (2 : Fin 4)
  have h3 : littleEndianWord (canonicalOutput value) (3 : Fin 8) =
      (canonicalLimbs value 3 : Nat) := by
    simpa using canonical_output_first_four_words value (3 : Fin 4)
  have hlt0 : (canonicalLimbs value 0 : Nat) < 2147483648 :=
    lt_trans (canonicalLimbs value 0).isLt (by norm_num [P])
  have hlt1 : (canonicalLimbs value 1 : Nat) < 2147483648 :=
    lt_trans (canonicalLimbs value 1).isLt (by norm_num [P])
  have hlt2 : (canonicalLimbs value 2 : Nat) < 2147483648 :=
    lt_trans (canonicalLimbs value 2).isLt (by norm_num [P])
  have hlt3 : (canonicalLimbs value 3 : Nat) < 2147483648 :=
    lt_trans (canonicalLimbs value 3).isLt (by norm_num [P])
  simp [blockWords, canonicalLimbList, maskedM31, m31MaskModulus,
    h0, h1, h2, h3, Nat.mod_eq_of_lt hlt0, Nat.mod_eq_of_lt hlt1,
    Nat.mod_eq_of_lt hlt2, Nat.mod_eq_of_lt hlt3]

theorem limbs_four_canonical_prefix
    (tape : FSBoundedTranscript.Tape)
    (transcript : FSBoundedTranscript.Transcript)
    (value : K) (suffix : List Nat) :
    (FSBoundedTranscript.limbs tape 4
      ⟨transcript, canonicalLimbList value ++ suffix⟩).1 =
      some (canonicalLimbList value) := by
  have hne (j : Fin 4) : (canonicalLimbs value j : Nat) ≠ 2147483647 := by
    exact ne_of_lt (canonicalLimbs value j).isLt
  simp [FSBoundedTranscript.limbs, FSBoundedTranscript.limb,
    FSBoundedTranscript.nextWord, canonicalLimbList,
    hne 0, hne 1, hne 2, hne 3]

theorem candidate_of_first_canonical_output
    (tape : FSBoundedTranscript.Tape)
    (transcript : FSBoundedTranscript.Transcript)
    (value : K)
    (firstOutput : (FSBoundedTranscript.squeeze tape transcript).1 =
      canonicalOutput value) :
    (FSNonzeroQM31.candidate tape transcript).1 = .ok value := by
  have wordsDecomposition :
      FSBoundedTranscript.words (canonicalOutput value) =
        canonicalLimbList value ++
          (FSBoundedTranscript.words (canonicalOutput value)).drop 4 := by
    rw [← words_take_four_canonical_output value]
    exact (List.take_append_drop 4 _).symm
  simp only [FSNonzeroQM31.candidate, FSBoundedTranscript.challenge]
  rw [firstOutput]
  rw [wordsDecomposition]
  rw [limbs_four_canonical_prefix]
  simp only [assemble_canonical_limbs]

#print axioms canonical_limbs_reconstruct
#print axioms assemble_canonical_limbs
#print axioms canonical_output_first_four_words
#print axioms words_take_four_canonical_output
#print axioms limbs_four_canonical_prefix
#print axioms candidate_of_first_canonical_output

/- `candidate_of_first_canonical_output` is deterministic.  Its premise is
   deliberately the actual first squeeze answer, not a role label or an
   unproved freshness assertion.  The FS restoration layer must produce that
   premise only in the correctly programmed prior-adversary-query branch. -/

end
end AspisV8Completion.AlphaDigestEncodingProbe
