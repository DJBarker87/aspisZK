import KMZ_Growth
set_option autoImplicit false
namespace KMZ_Clone16
open KMX_CopyMeaning KMY_WindowComposition
theorem result {α : Type} (src : List α) (h : src.length=16) :
 appendLoop [] src = src ∧ (appendLoop [] src).length=16 := by
 constructor
 · exact KMY_VectorComposition.to_vec_value src
 · rw [KMY_VectorComposition.to_vec_value]
   exact h
#print axioms result
end KMZ_Clone16
