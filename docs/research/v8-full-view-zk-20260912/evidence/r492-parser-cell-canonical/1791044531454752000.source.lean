import AspisV8R19.R481NativeQM31Cell
import AspisV8R19.R487ParserScalarMask

/-! Exact scalar-mask and packed-cell correspondence. This does not establish
that the native parser builds the supplied list or justify native alignment,
allocation, iteration, or error propagation. -/
set_option autoImplicit false

namespace AspisV8R19.R492ParserCellCanonical

open Aeneas Aeneas.Std
open AspisR156FullFreeze AspisR156FullFreeze.aspis_core
open AspisV8R19.R481NativeQM31Cell

def lanes (x : field.QM31) : List U32 := [x.c0.a, x.c0.b, x.c1.a, x.c1.b]

def canonicalQM31 (x : field.QM31) : Prop :=
  x.c0.a.val < 2147483647 ∧
  x.c0.b.val < 2147483647 ∧
  x.c1.a.val < 2147483647 ∧
  x.c1.b.val < 2147483647

theorem canonicalQM31_iff_lanes (x : field.QM31) :
    canonicalQM31 x ↔ ∀ w ∈ lanes x, w.val < 2147483647 := by
  simp [canonicalQM31, lanes]

theorem parserCellMask_accepts_iff (cells : List field.QM31) :
    UScalar.shiftRight
        (AspisV8R19.R487ParserScalarMask.scalarAccumulated 0#u32
          (cells.flatMap lanes)) 31 = .ok 0#u32 ↔
      ∀ x ∈ cells, canonicalQM31 x := by
  rw [AspisV8R19.R487ParserScalarMask.scalar_mask_complete]
  constructor
  · intro h x hx
    apply (canonicalQM31_iff_lanes x).2
    intro w hw
    apply h w
    exact List.mem_flatMap.mpr ⟨x, hx, hw⟩
  · intro h w hw
    rcases List.mem_flatMap.mp hw with ⟨x, hx, hword⟩
    exact (canonicalQM31_iff_lanes x).1 (h x hx) w hword

theorem lanes_decode_packed_words (a b c d : BitVec 32) :
    lanes (decodeQM31 (packWords a b c d)) =
      [decodeM31 a, decodeM31 b, decodeM31 c, decodeM31 d] := by
  simp [lanes, decodeQM31, packWords_lane0, packWords_lane1,
    packWords_lane2, packWords_lane3]

theorem decoded_packed_canonical_iff (a b c d : BitVec 32) :
    canonicalQM31 (decodeQM31 (packWords a b c d)) ↔
      a.toNat < 2147483647 ∧ b.toNat < 2147483647 ∧
      c.toNat < 2147483647 ∧ d.toNat < 2147483647 := by
  simp [canonicalQM31, decodeQM31, decodeM31,
    packWords_lane0, packWords_lane1, packWords_lane2, packWords_lane3]

def canonicalPacked (x : BitVec 128) : Prop :=
  (x.extractLsb' 0 32).toNat < 2147483647 ∧
  (x.extractLsb' 32 32).toNat < 2147483647 ∧
  (x.extractLsb' 64 32).toNat < 2147483647 ∧
  (x.extractLsb' 96 32).toNat < 2147483647

theorem decoded_cell_canonical_iff (x : BitVec 128) :
    canonicalQM31 (decodeQM31 x) ↔ canonicalPacked x := by
  have h := decoded_packed_canonical_iff (x.extractLsb' 0 32)
    (x.extractLsb' 32 32) (x.extractLsb' 64 32) (x.extractLsb' 96 32)
  simpa only [packWords_extracted, canonicalPacked] using h

theorem packed_list_mask_exact (cells : List (BitVec 128)) :
    UScalar.shiftRight
        (AspisV8R19.R487ParserScalarMask.scalarAccumulated 0#u32
          ((cells.map decodeQM31).flatMap lanes)) 31 = .ok 0#u32 ↔
      ∀ x ∈ cells, canonicalPacked x := by
  rw [parserCellMask_accepts_iff]
  constructor
  · intro h x hx
    exact (decoded_cell_canonical_iff x).mp
      (h (decodeQM31 x) (List.mem_map.mpr ⟨x, hx, rfl⟩))
  · intro h y hy
    rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
    exact (decoded_cell_canonical_iff x).mpr (h x hx)

#print axioms canonicalPacked
#print axioms decoded_cell_canonical_iff
#print axioms packed_list_mask_exact

#print axioms lanes
#print axioms canonicalQM31
#print axioms canonicalQM31_iff_lanes
#print axioms parserCellMask_accepts_iff
#print axioms lanes_decode_packed_words
#print axioms decoded_packed_canonical_iff

end AspisV8R19.R492ParserCellCanonical
