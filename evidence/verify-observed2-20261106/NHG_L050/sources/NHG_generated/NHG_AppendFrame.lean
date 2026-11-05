import NHG_CopyFrame
set_option autoImplicit false
namespace AspisR1.NHG_AppendFrame

theorem grow_append {A : Type} (src fresh bytes : Nat → A)
 (oldSize newSize n count k : Nat) (old : n≤oldSize)
 (new : n+count≤newSize) (inside : k<n+count) :
 KMX_CopyMeaning.loop (fun j=>bytes (j-n))
  (KMX_CopyMeaning.loop src fresh 0 (min oldSize newSize)) n count k =
 if k<n then src k else bytes (k-n) := by
 rw [KMX_CopyMeaning.loop_spec]
 by_cases early : k<n
 · rw [if_neg (by omega),if_pos early]
   exact NHG_CopyFrame.realloc_initialized src fresh oldSize newSize n k old (by omega) early
 · rw [if_pos (by omega),if_neg early]

theorem old_prefix {A : Type} (src fresh bytes : Nat → A)
 (oldSize newSize n count k : Nat) (old : n≤oldSize)
 (new : n+count≤newSize) (inside : k<n) :
 KMX_CopyMeaning.loop (fun j=>bytes (j-n))
  (KMX_CopyMeaning.loop src fresh 0 (min oldSize newSize)) n count k=src k := by
 rw [grow_append src fresh bytes oldSize newSize n count k old new (by omega),if_pos inside]

theorem new_suffix {A : Type} (src fresh bytes : Nat → A)
 (oldSize newSize n count k : Nat) (old : n≤oldSize)
 (new : n+count≤newSize) (inside : n≤k ∧ k<n+count) :
 KMX_CopyMeaning.loop (fun j=>bytes (j-n))
  (KMX_CopyMeaning.loop src fresh 0 (min oldSize newSize)) n count k=bytes (k-n) := by
 rw [grow_append src fresh bytes oldSize newSize n count k old new inside.2,if_neg (by omega)]

#print axioms grow_append
#print axioms old_prefix
#print axioms new_suffix
end AspisR1.NHG_AppendFrame
