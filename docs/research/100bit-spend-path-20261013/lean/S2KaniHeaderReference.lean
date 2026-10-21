import Aeneas

/-! Owned header reference emitted by the pinned translator. The definition
below is copied verbatim from AspisS2HeaderRef/Funs.lean. No generated resource
options are imported. The source-cut comparison does not identify arbitrary
headline decisions with this header check. -/
set_option autoImplicit false
namespace AspisS2HeaderRef
open Aeneas Aeneas.Std Result

def header_reference
  (length : Std.Usize) (magic : Bool) (tag : Std.U8) (tail : Bool) :
  Result Bool
  := do
  if length = 57607#usize
  then if magic
       then if tag = 2#u8
            then ok tail
            else ok false
       else ok false
  else ok false

theorem header_rejects (length : Usize) (magic tail : Bool) (tag : U8)
    (htag : tag ≠ 2#u8) : header_reference length magic tag tail = ok false := by
  simp [header_reference, htag]

theorem header_accepts_iff (length : Usize) (magic tail : Bool) (tag : U8) :
    header_reference length magic tag tail = ok true ↔
      length = 57607#usize ∧ magic = true ∧ tag = 2#u8 ∧ tail = true := by
  unfold header_reference
  split <;> rename_i hl
  · cases magic <;> simp [hl]
    split <;> simp_all
  · simp [hl]

#print axioms header_rejects
#print axioms header_accepts_iff
end AspisS2HeaderRef
