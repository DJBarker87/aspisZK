import S8OwnedP6StrictScanModel
import OraclePortCompactDraft

/-! Byte-order bridge from the strict four-limb codec to the frozen parser.
Only four or sixteen bytes are reduced; whole proofs are handled symbolically. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.S8JoinCompactChunks
open Aeneas Aeneas.Std
open RetainedFieldByteCodec CandidateParserByteOrder OraclePortCompactDraft

/-- Literal stored bytes of an extracted slice. -/
def wire (s : Slice U8) : Bytes := s.val.map AspisV8R19.SqueezeOracleBridge.decodeByte

/-- The four-byte fold and the retained limb decoder use the same endian order. -/
theorem little_four (b : WordBytes) :
    little (List.ofFn b) = (decodeWordLE b).val := by
  simp [List.ofFn_succ, little, decodeWordLE]
  omega

/-- Sixteen-byte codec acceptance equals four canonical stored words. -/
theorem codec_canonical (b : QM31Bytes) :
    (decodeQM31LE b).isSome = true ↔ canonical (List.ofFn b) := by
  have limb (k : Fin 4) :
      little (slice (List.ofFn b) (4*k.val) 4) =
        (decodeWordLE (qm31LimbBytes b k)).val := by
    fin_cases k <;>
      simp [slice, List.ofFn_succ, little, decodeWordLE, qm31LimbBytes,
        limbByteIndex] <;> omega
  have hc : (decodeQM31LE b).isSome = true ↔
      ∀ k : Fin 4, (decodeWordLE (qm31LimbBytes b k)).val < 2147483647 := by
    unfold decodeQM31LE
    split <;> simp_all [m31Modulus,rawCandidateCount]
  rw [hc]
  simp only [canonical,List.length_ofFn]
  constructor
  · intro h
    refine ⟨by decide,?_⟩
    intro j hj
    have hj' : j < 4 := by simpa only [List.mem_range] using hj
    simpa only [limb ⟨j,hj'⟩] using h ⟨j,hj'⟩
  · intro h k
    rw [← limb k]
    exact h.2 k.val (List.mem_range.mpr k.isLt)

#print axioms little_four
#print axioms codec_canonical
end AspisR1.S8JoinCompactChunks
end
