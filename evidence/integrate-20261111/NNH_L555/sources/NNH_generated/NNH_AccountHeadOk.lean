import NNH_MAccountCarrier
set_option autoImplicit false
namespace NNH_AccountHeadOk
open Aeneas Aeneas.Std AdapterRw NNH_ModelCarrier

theorem value (xs : Slice r1_pool_adapter.owned.OwnedAccount) (proof : RSL.OwnedAccount)
 (success : (accounts xs).head?=some proof) :
 ∃ native,xs.val.head?=some native ∧ account native=proof := by
 cases source : xs.val with
 | nil => simp only [accounts,source,List.map_nil,List.head?_nil] at success; cases success
 | cons native rest =>
  refine ⟨native,?_,?_⟩
  · simp only [source,List.head?_cons]
  · simpa only [accounts,source,List.map_cons,List.head?_cons,Option.some.injEq] using success
#print axioms value
end NNH_AccountHeadOk
