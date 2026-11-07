import NMX_R3_LaneAllocation
set_option autoImplicit false
namespace NMX_R3_NativeWindow
open RSL

/-- The 128-byte prefix used by the native segment contains every read before
its first child call. This includes the child's exact 32-byte root argument. -/
theorem read (b : Bytes) (i : Nat) (inside : i < 128) :
 (b.take 128).getD i 0 = b.getD i 0 := by
 simp only [List.getD, List.getElem?_take, inside, ↓reduceIte]

theorem window (b : Bytes) (s n : Nat) (inside : s+n ≤ 128) :
 slice (b.take 128) s (s+n) = slice b s (s+n) := by
 apply List.ext_getElem
 · simp only [slice,List.length_take,List.length_drop]
   omega
 · intro i hi hj
   have h : i < n := by
    simp only [slice,List.length_take,List.length_drop] at hj
    omega
   simp only [slice, show s+n-s=n by omega, List.getElem_take, List.getElem_drop]

theorem root_window (b : Bytes) :
 slice ((b.take 128).drop 80) 16 48 = slice (b.drop 80) 16 48 := by
 change (((b.take 128).drop 80).drop 16).take 32 = ((b.drop 80).drop 16).take 32
 simp only [List.drop_drop]
 exact window b 96 32 (by decide)

/-- The source loop's arbitrary-level address fits the tree, with neither a
caller extent assumption nor a success assumption on the digest. -/
theorem frontier_window (level : Nat) (inside : level < 20) :
 48+32*level+32 ≤ 688 := by omega

/-- The source views used at the prefix cut are safely internal after the first
check. This lemma records source geometry, not a RowSpec domain restriction. -/
theorem extent (b : Bytes) (passed : b.length = 768) :
 128 ≤ b.length ∧ (b.drop 80).length = 688 ∧
 (slice b 40 72).length = 32 ∧ (slice (b.drop 80) 16 48).length = 32 := by
 simp only [slice,List.length_take,List.length_drop,passed]
 decide
#print axioms read
#print axioms window
#print axioms root_window
#print axioms frontier_window
#print axioms extent
end NMX_R3_NativeWindow
