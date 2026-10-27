import RPv_FIx_ReconstructPrefixModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_ReconstructMeaning
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)

theorem value (view : Array NQ 16#usize) (out : NQ) (hc : ∀ x∈view.val,Canon x)
    (success : pool_v1.pair_forest_semantic_terminal.reconstruct_10 view=ok out) :
    Canon out ∧ decode out=R0P.valueReconstruct10 (fun i=>FIv_NativeArray.value view i.val) := by
  have source := FIx_ReconstructValue.value view out hc success
  refine ⟨source.1,?_⟩
  rw [source.2]
  unfold FIx_ReconstructValue.model
  rw [FIx_ReconstructPrefixModel.value view 9 (by have h:=view.property;change view.val.length=16 at h;omega)]
  exact SelectorReconstructIndexModel.reconstructIndexed_nine_eq_valueReconstruct10 (FIv_NativeArray.value view)
#print axioms value
end AspisR1.FIx_ReconstructMeaning
end
