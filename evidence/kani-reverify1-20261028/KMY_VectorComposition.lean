import KMY_CheckpointComposition
set_option autoImplicit false
namespace KMY_VectorComposition
open KMX_CopyMeaning

theorem to_vec_value {α : Type} (src : List α) : appendLoop [] src = src := by
  rw [append_spec, List.nil_append]

theorem growth_retains (old garbage : Nat → Nat) (oldCapacity newCapacity j : Nat)
    (growth : oldCapacity ≤ newCapacity) (live : j < oldCapacity) :
    loop old garbage 0 (min oldCapacity newCapacity) j = old j := by
  rw [realloc_prefix, Nat.min_eq_left growth, if_pos live]

theorem six_lengths {α : Type} (a b c d e f : List α)
    (ha : a.length=32) (hb : b.length=32) (hc : c.length=32)
    (hd : d.length=32) (he : e.length=32) (hf : f.length=32) :
    (appendLoop (appendLoop (appendLoop (appendLoop
      (appendLoop (appendLoop [] a) b) c) d) e) f).length = 192 := by
  simp only [append_spec, List.length_append, List.length_nil, ha, hb, hc, hd, he, hf]

theorem selected_prefix_bound (i : Nat) (h : i<64) : 712+16*i+16 ≤ 1736 := by omega

theorem scalar_prefix_bound (len : Nat) (h : len≤1720) : len+16≤1736 := by omega

theorem wide_prefix_bound (len : Nat) (h : len≤1704) : len+32≤1736 := by omega

theorem query_prefix_bound (len : Nat) (h : len≤1732) : len+4≤1736 := by omega

#print axioms to_vec_value
#print axioms growth_retains
#print axioms six_lengths
#print axioms selected_prefix_bound
#print axioms scalar_prefix_bound
#print axioms wide_prefix_bound
#print axioms query_prefix_bound
end KMY_VectorComposition
