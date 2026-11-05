import NGU_Carriers
open Aeneas Aeneas.Std Result
open NGU_Carriers
set_option autoImplicit false
namespace NGU_ArrayMap

theorem set {A B : Type} {N : Usize} (f : A → B) (a : Array A N) (i : Usize) (x : A) :
 arr f (a.set i x) = (arr f a).set i (f x) := by
 apply Subtype.ext
 simp only [arr,Array.set]
 exact List.map_set

theorem repeated {A B : Type} (f : A → B) (N : Usize) (x : A) :
 arr f (Array.repeat N x) = Array.repeat N (f x) := by
 apply Subtype.ext
 simp only [arr,Array.repeat,List.map_replicate]

#print axioms set
#print axioms repeated
end NGU_ArrayMap
