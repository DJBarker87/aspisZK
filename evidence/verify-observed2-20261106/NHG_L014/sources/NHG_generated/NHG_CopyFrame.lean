import NHG_Lengths
import KMX_CopyMeaning
set_option autoImplicit false
namespace AspisR1.NHG_CopyFrame
/-- The native one-byte window is the exact raw MaybeUninit transfer in the
pinned KMX realloc loop. Its logical write affects only that index. -/
theorem step {A : Type} (src dst : Nat → A) (i k : Nat) :
 KMX_CopyMeaning.write dst i (src i) k = if k=i then src i else dst k := rfl

theorem realloc_initialized {A : Type} (src dst : Nat → A)
 (oldSize newSize n k : Nat) (old : n≤oldSize) (new : n≤newSize) (inside : k<n) :
 KMX_CopyMeaning.loop src dst 0 (min oldSize newSize) k=src k := by
 rw [KMX_CopyMeaning.realloc_prefix,if_pos]
 omega

/-- General prefix length and allocation sizes. The four appended bytes are
written after the realloc-preserved prefix on THIS resulting allocation. -/
theorem grow_append4 {A : Type} (src fresh bytes : Nat → A)
 (oldSize newSize n k : Nat) (old : n≤oldSize) (new : n+4≤newSize) (inside : k<n+4) :
 KMX_CopyMeaning.loop (fun j=>bytes (j-n))
  (KMX_CopyMeaning.loop src fresh 0 (min oldSize newSize)) n 4 k =
 if k<n then src k else bytes (k-n) := by
 rw [KMX_CopyMeaning.loop_spec]
 by_cases early : k<n
 · rw [if_neg (by omega),if_pos early]
   exact realloc_initialized src fresh oldSize newSize n k old (by omega) early
 · rw [if_pos (by omega),if_neg early]

#print axioms step
#print axioms realloc_initialized
#print axioms grow_append4
end AspisR1.NHG_CopyFrame
