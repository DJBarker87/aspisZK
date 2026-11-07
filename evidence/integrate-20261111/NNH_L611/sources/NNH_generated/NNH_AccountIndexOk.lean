import NNH_AccountHeadOk
import NNH_OptionOk
import NND_ReturnedDomain
set_option autoImplicit false
namespace NNH_AccountIndexOk
open Aeneas Aeneas.Std AdapterRw NNH_ModelCarrier NND_Returned

theorem value (xs : Slice r1_pool_adapter.owned.OwnedAccount) (i : Usize) (owned : RSL.OwnedAccount)
 (success : indexValue (accounts xs) i.val=.ok owned) :
 ∃ native,Slice.index_usize xs i=.ok native ∧ account native=owned := by
 have mapped := NNH_OptionOk.value _ _ _ success
 change (xs.val.map account)[i.val]?=some owned at mapped
 rw [List.getElem?_map] at mapped
 cases source : xs.val[i.val]? with
 | none => simp only [source,Option.map_none] at mapped; cases mapped
 | some native =>
  simp only [source,Option.map_some,Option.some.injEq] at mapped
  refine ⟨native,?_,mapped⟩
  unfold Slice.index_usize
  simp only [source]
#print axioms value
end NNH_AccountIndexOk
