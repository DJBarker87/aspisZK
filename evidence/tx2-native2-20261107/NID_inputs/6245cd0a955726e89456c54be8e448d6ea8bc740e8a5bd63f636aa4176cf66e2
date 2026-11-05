import NHV_COMBINED_IMPORT
set_option autoImplicit false
namespace NID_RawOffsetCover
/-- The seven native offset partitions cover EVERY valid32-byte raw read in
checkpoint1768, including the last offset1736. No caller domain is narrowed. -/
theorem cover (offset : Nat) (valid : offset+32≤1768) :
 ∃ block, block<7 ∧ 256*block≤offset ∧ offset<256*(block+1) := by
 refine ⟨offset/256,?_,?_,?_⟩ <;> omega

theorem unique (offset left right : Nat)
 (l0 : 256*left≤offset) (l1 : offset<256*(left+1))
 (r0 : 256*right≤offset) (r1 : offset<256*(right+1)) : left=right := by omega
#print axioms cover
#print axioms unique
end NID_RawOffsetCover
