import NHY_FieldRead
set_option autoImplicit false
namespace NHY_WindowTransport
open Aeneas Aeneas.Std Result

def start (size width off : Nat) : Nat := min off (size-width)
def relative (size width off : Nat) : Nat := off-start size width off

theorem bounds (size width field off : Nat) (small : field ≤ width)
    (fits : width ≤ size) (legal : off+field ≤ size) :
    start size width off+width ≤ size ∧
    relative size width off+field ≤ width ∧
    start size width off+relative size width off=off := by
  simp only [relative,start]
  omega

/-- Same source list window, never a fresh or oversized backing allocation. -/
theorem nested (b : Slice U8) (a n s w : Nat) (fit : s+w ≤ n) :
    NHY_SliceRead.segment (NHY_SliceRead.segment b a n) s w=
      NHY_SliceRead.segment b (a+s) w := by
  apply Subtype.ext
  simp only [NHY_SliceRead.segment,List.drop_take,List.drop_drop,List.take_take]
  have h : w ≤ n-s := by omega
  simp only [Nat.min_eq_left h]

theorem field (b : Slice U8) (width count off : Nat)
    (small : count ≤ width) (fit : width ≤ b.val.length)
    (legal : off+count ≤ b.val.length) :
    NHY_SliceRead.segment
      (NHY_SliceRead.segment b (start b.val.length width off) width)
      (relative b.val.length width off) count = NHY_SliceRead.segment b off count := by
  obtain ⟨_,frame,same⟩:=bounds b.val.length width count off small fit legal
  rw [nested _ _ _ _ _ frame,same]

theorem array_domain (size off : Nat) (size_ok : size=256 ∨ size=320)
    (legal : off+32 ≤ size) :
    start size 64 off+64 ≤ size ∧ relative size 64 off ≤ 32 ∧
    start size 64 off+relative size 64 off=off := by
  have b:=bounds size 64 32 off (by omega) (by omega) legal
  omega

theorem word_domain (size off : Nat) (size_ok : size=256 ∨ size=320)
    (legal : off+8 ≤ size) :
    start size 16 off+16 ≤ size ∧ relative size 16 off ≤ 8 ∧
    start size 16 off+relative size 16 off=off := by
  have b:=bounds size 16 8 off (by omega) (by omega) legal
  omega

#print axioms bounds
#print axioms nested
#print axioms field
#print axioms array_domain
#print axioms word_domain
end NHY_WindowTransport
