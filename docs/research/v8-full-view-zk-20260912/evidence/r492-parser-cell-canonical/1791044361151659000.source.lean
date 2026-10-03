import AspisV8R19.R481NativeQM31Cell
import AspisV8R19.R487ParserScalarMask

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

#print axioms lanes
#print axioms canonicalQM31
#print axioms canonicalQM31_iff_lanes
#print axioms parserCellMask_accepts_iff
#print axioms lanes_decode_packed_words
#print axioms decoded_packed_canonical_iff

end AspisV8R19.R492ParserCellCanonical
