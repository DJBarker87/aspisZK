import NKR_SumIntervals
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_SumTagPartition
open NKR_SumIntervals

theorem first (c : Fin 30) : NJL_TagData.first c=off c.val := by
 have h : c.val≤30 := Nat.le_of_lt c.isLt
 simp only [off,Nat.min_eq_left h,NJL_TagData.first]
 rfl

theorem last (c : Fin 30) : NJL_TagData.last c=off (c.val+1) := by
 have h : c.val+1≤30 := c.isLt
 simp only [off,Nat.min_eq_left h,NJL_TagData.last]
 rfl

theorem flatMap_map {A B C : Type} (f : B → List C) (v : A → B) (xs : List A) :
 (xs.map v).flatMap f=xs.flatMap (fun a=>f (v a)) := by
 induction xs with
 | nil => rfl
 | cons x xs ih => simp only [List.map_cons,List.flatMap_cons,ih]

/-- The30frozen contiguous buckets cover all272tag terms exactly once.
Proof uses generic range concatenation and Fin.val injectivity,never a
concrete272-cell kernel enumeration. -/
theorem source : (List.finRange 30).flatMap NJL_TagData.indices=List.finRange 272 := by
 apply lists_ext
 rw [map_flatMap]
 have ranges : (List.finRange 30).flatMap (fun c=>(NJL_TagData.indices c).map Fin.val)=intervals off 30 := by
  unfold intervals
  rw [←fin_values 30,flatMap_map]
  apply congrArg (fun f : Fin 30 → List Nat=>(List.finRange 30).flatMap f)
  funext c
  rw [NJL_TagData.range_values,first,last]
 rw [ranges,thirty,fin_values]

#print axioms first
#print axioms last
#print axioms flatMap_map
#print axioms source
end AspisR1.NKR_SumTagPartition
end
