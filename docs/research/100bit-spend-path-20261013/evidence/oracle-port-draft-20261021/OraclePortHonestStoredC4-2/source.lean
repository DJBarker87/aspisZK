import OraclePortHonestRowsC4

/-! Explicit canonical zero-field compact layout. This witnesses syntax parser
inhabitation, not semantic/Merkle acceptance or a valid spend. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortHonestStoredC4
open AspisV8R19.DuplexFrames
open OraclePortCompactDraft OraclePortHonestRowsC4
attribute [local instance] Classical.propDecidable

def encodedSize : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, row => 5 + storedSize row + encodedSize n (row+1)

theorem encode_length (n row : Nat) : (encode n row).length = encodedSize n row := by
  induction n generalizing row with
  | zero => rfl
  | succ n ih => simp only [encode,encodedSize,List.length_append,header_length,
      List.length_replicate,ih]

theorem semantic_length : (encode 27 0).length = 6983 := by
  rw [encode_length]
  norm_num [encodedSize,storedSize,rowShape]

def wireHeader : Bytes := [82,49,80,51,67,66,49,56,2,0,0,0,0,0,0,0]
def front : Bytes := (wireHeader ++ List.replicate 32 0) ++ encode 27 0
def wire : Bytes := front ++ List.replicate 50576 0

theorem front_length : front.length = 7031 := by
  simp only [front,List.length_append,List.length_replicate,semantic_length]
  rfl

theorem wire_length : wire.length = 57607 := by
  simp only [wire,List.length_append,front_length,List.length_replicate]

theorem header_valid : OraclePortHeader.accepts wire = true := by
  apply (OraclePortHeader.accepts_iff wire).mpr
  refine ⟨wire_length,?_,?_,?_⟩ <;>
    simp [wire,front,wireHeader,OraclePortHeader.magic,List.take_append,List.drop_append]

theorem zero_slice (offset size : Nat) (lo : 7031 ≤ offset) (hi : offset+size ≤ 57607) :
    slice wire offset size = List.replicate size 0 := by
  unfold slice wire
  rw [List.drop_append]
  rw [List.drop_eq_nil_of_le (by rw [front_length]; exact lo),List.nil_append]
  simp only [List.drop_replicate,List.take_replicate,front_length]
  congr 1
  omega

theorem scan_valid : scan wire := by
  have h0 := canonical_zeros 464 (by decide)
  have h1 := canonical_zeros 256 (by decide)
  have h2 := canonical_zeros 2272 (by decide)
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [zero_slice 7031 464 (by decide) (by decide)] using h0
  · simpa only [zero_slice 7495 256 (by decide) (by decide)] using h1
  · simpa only [zero_slice 7783 2272 (by decide) (by decide)] using h2
  · intro j hj
    have bound := List.mem_range.mp hj
    rw [zero_slice (10055+j*832) 832 (by omega) (by omega)]
    constructor
    · simpa [List.take_replicate] using canonical_zeros 608 (by decide)
    · simpa [slice,List.drop_replicate,List.take_replicate] using canonical_zeros 128 (by decide)

theorem semantic_slice : slice wire 48 6983 = encode 27 0 := by
  have hl : (wireHeader ++ List.replicate 32 (0 : AspisV8R19.DuplexFrames.Byte)).length = 48 := by rfl
  unfold slice wire front
  rw [List.append_assoc, ← hl,List.drop_append_length,← semantic_length,List.take_append_length]

theorem parse_honest : parse wire = some ⟨wire,decoded 27 0⟩ := by
  simp only [parse,header_valid,Bool.true_eq_false,↓reduceIte,scan_valid,
    not_true_eq_false,semantic_slice,roundtrip]
  rfl

/-- Inhabited independently of all transcript alignment or acceptance laws. -/
theorem parser_nonvacuous : ∃ p : Parsed, parse wire = some p :=
  ⟨_,parse_honest⟩

#print axioms encode_length
#print axioms semantic_length
#print axioms front_length
#print axioms wire_length
#print axioms header_valid
#print axioms zero_slice
#print axioms scan_valid
#print axioms semantic_slice
#print axioms parse_honest
#print axioms parser_nonvacuous
end AspisR1.OraclePortHonestStoredC4
end
