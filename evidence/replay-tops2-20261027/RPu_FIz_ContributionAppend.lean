import RPu_FIz_ContributionList
import RPu_FIz_PackLinear
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIz_ContributionAppend
open FIv_NativeValue (K)
theorem value (xs ys : List K) (start group : Nat) :
    FIz_ContributionList.fromList (xs++ys) start group=
      FIz_ContributionList.fromList xs start group+
      FIz_ContributionList.fromList ys (start+xs.length) group := by
  unfold FIz_ContributionList.fromList
  rw [←FIz_PackLinear.add]
  apply congrArg FIx_PreweightedPack.pack
  funext i
  by_cases lo : start≤4*group+i.val
  · simp only [if_pos lo]
    by_cases hi : 4*group+i.val<start+xs.length
    · have nlo : ¬start+xs.length≤4*group+i.val := by omega
      simp only [if_neg nlo,add_zero]
      rw [List.getElem?_append_left (by omega)]
    · have nlo : start+xs.length≤4*group+i.val := by omega
      simp only [if_pos nlo]
      have none : xs[4*group+i.val-start]?=none := List.getElem?_eq_none (by omega)
      rw [List.getElem?_append_right (by omega),none]
      simp only [Option.getD_none,zero_add]
      congr 2
      omega
  · have nlo : ¬start+xs.length≤4*group+i.val := by omega
    simp only [if_neg lo,if_neg nlo,zero_add]
#print axioms value
end AspisR1.FIz_ContributionAppend
end
