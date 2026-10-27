import RPu_FIx_ReconstructSource
import RPu_FIx_ReconstructSliceValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_ReconstructValue
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)

def model (view : Array NQ 16#usize) : K :=
  FIx_ReconstructFold.model (view.val.take 9) (FIv_NativeArray.value view 9)

theorem value (view : Array NQ 16#usize) (out : NQ) (hc : ∀ x∈view.val,Canon x)
    (success : pool_v1.pair_forest_semantic_terminal.reconstruct_10 view=ok out) :
    Canon out ∧ decode out=model view := by
  obtain ⟨headSlice,seed,hprefix,hseed,hfold⟩ := FIx_ReconstructSource.reached view out success
  have hp : headSlice.val=view.val.take 9 := FIx_ReconstructSlice.value view headSlice hprefix
  have hcanon : ∀ x∈headSlice.val,Canon x := by
    intro x hx
    rw [hp] at hx
    exact hc x (List.mem_of_mem_take hx)
  have hseedcanon := FIv_NativeArray.canonical view 9#usize seed hc hseed
  have folded := FIx_ReconstructFold.value headSlice.val headSlice.property seed out () hcanon hseedcanon hfold
  refine ⟨folded.1,?_⟩
  rw [folded.2,hp,←FIv_NativeArray.read view 9#usize seed hseed]
  rfl
#print axioms value
end AspisR1.FIx_ReconstructValue
end
