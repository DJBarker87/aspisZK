import SCE_Experiment
set_option autoImplicit false
namespace AspisR1.SCE_ByteSuffix
open Aeneas Aeneas.Std
/-- Symbolic prefix erasure before instantiating a large native byte list. -/
theorem replicate_prefix (n : Nat) (head : U8) (tail : List U8) :
    (MultiproofConeCanonical.bytesOf (List.replicate n head ++ tail)).drop n =
      MultiproofConeCanonical.bytesOf tail := by
  simp only [MultiproofConeCanonical.bytesOf,List.map_append,List.map_replicate,
    List.drop_append,List.length_replicate,List.drop_replicate,Nat.sub_self,
    List.replicate_zero,List.nil_append,List.drop_zero]
#print axioms replicate_prefix
end AspisR1.SCE_ByteSuffix
