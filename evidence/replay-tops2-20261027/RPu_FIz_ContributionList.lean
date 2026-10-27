import RPu_FIz_SelectedList
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIz_ContributionList
open FIv_NativeValue (K)
def fromList (xs : List K) (start group : Nat) : K :=
  FIx_PreweightedPack.pack (fun i=> if start≤4*group+i.val then
    (xs[4*group+i.val-start]?).getD 0 else 0)
theorem value {n : Nat} (a : Fin n → K) (start group : Nat) :
    FIx_SelectedMeaning.contribution a start group=fromList (List.ofFn a) start group := by
  unfold FIx_SelectedMeaning.contribution fromList
  apply congrArg FIx_PreweightedPack.pack
  funext i
  exact FIz_SelectedList.value a start group i.val
#print axioms value
end AspisR1.FIz_ContributionList
end
