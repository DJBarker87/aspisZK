import S8OwnedP6StrictScanModel
import OraclePortCompactDraft

/-! Byte-order bridge from the strict four-limb codec to the frozen parser.
Only four or sixteen bytes are reduced; whole proofs are handled symbolically. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.S8JoinCompactChunks
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
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
        limbByteIndex, finProdFinEquiv] <;> omega
  have hc : (decodeQM31LE b).isSome = true ↔
      ∀ k : Fin 4, (decodeWordLE (qm31LimbBytes b k)).val < 2147483647 := by
    unfold decodeQM31LE
    split
    · rename_i h
      exact ⟨fun _ => h,fun _ => rfl⟩
    · rename_i h
      constructor
      · intro bad; cases bad
      · intro good; exact False.elim (h good)
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

theorem slice_slice (b : Bytes) (a n c k : Nat) (bound : c+k ≤ n) :
    slice (slice b a n) c k = slice b (a+c) k := by
  simp only [slice, List.drop_take, List.drop_drop, List.take_take]
  rw [Nat.min_eq_left (by omega : k ≤ n-c)]

theorem array_wire (arr : Array U8 16#usize) :
    wire (Array.to_slice arr) = List.ofFn (arrayBytes16 arr) := by
  have len : arr.val.length = 16 := arr.property
  apply List.ext_getElem
  · simp [wire,Array.to_slice,len]
  · intro i hi hj
    simp [wire,Array.to_slice,arrayBytes16]

theorem chunk_iff (bytes : Slice U8) (j : Nat) (bound : j < bytes.val.length/16) :
    S8OwnedP6StrictScanModel.CanonicalChunk bytes j ↔
      canonical (slice (wire bytes) (16*j) 16) := by
  have len : ((bytes.val.drop (16*j)).take 16).length = 16 := by
    simp only [List.length_take,List.length_drop]
    omega
  constructor
  · rintro ⟨arr,heq,hd⟩
    have hc := (codec_canonical (arrayBytes16 arr)).mp hd
    rw [← array_wire arr] at hc
    simpa only [wire,Array.to_slice,heq,List.map_take,List.map_drop,slice] using hc
  · intro hc
    let arr : Array U8 16#usize := ⟨(bytes.val.drop (16*j)).take 16,len⟩
    refine ⟨arr,rfl,(codec_canonical _).mpr ?_⟩
    rw [← array_wire arr]
    simpa only [wire,Array.to_slice,List.map_take,List.map_drop,slice] using hc

theorem canonical_chunks (b : Bytes) (multiple : b.length % 16 = 0) :
    canonical b ↔ ∀ j, j < b.length/16 → canonical (slice b (16*j) 16) := by
  have len (j : Nat) (hj : j < b.length/16) : (slice b (16*j) 16).length = 16 := by
    simp only [slice,List.length_take,List.length_drop]
    omega
  constructor
  · intro hc j hj
    refine ⟨by simp [len j hj],?_⟩
    intro k hk
    have hk' : k < 4 := by simpa only [List.mem_range,len j hj] using hk
    rw [slice_slice b (16*j) 16 (4*k) 4 (by omega)]
    have index : 16*j+4*k = 4*(4*j+k) := by omega
    rw [index]
    exact hc.2 (4*j+k) (List.mem_range.mpr (by omega))
  · intro hc
    refine ⟨by omega,?_⟩
    intro k hk
    have hk' : k < b.length/4 := List.mem_range.mp hk
    have hj : k/4 < b.length/16 := by omega
    have h := (hc (k/4) hj).2 (k%4) (List.mem_range.mpr (by
      rw [len (k/4) hj]
      exact Nat.mod_lt _ (by decide)))
    rw [slice_slice b (16*(k/4)) 16 (4*(k%4)) 4 (by omega)] at h
    have index : 16*(k/4)+4*(k%4) = 4*k := by omega
    simpa only [index] using h

#print axioms little_four
#print axioms codec_canonical
#print axioms slice_slice
#print axioms array_wire
#print axioms chunk_iff
#print axioms canonical_chunks
end AspisR1.S8JoinCompactChunks
end
