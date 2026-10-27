import FIx_ReconstructFold
import FIv_NativeArray
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_ReconstructSource
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)

theorem reached (view : Array NQ 16#usize) (out : NQ)
    (success : pool_v1.pair_forest_semantic_terminal.reconstruct_10 view=ok out) :
    ∃ prefix : Slice NQ, ∃ seed : NQ,
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice NQ)) view ⟨9#usize⟩=ok prefix ∧
      Array.index_usize view 9#usize=ok seed ∧
      FIx_ReconstructTraversal.fold ⟨prefix,0⟩ seed ()=ok out := by
  unfold pool_v1.pair_forest_semantic_terminal.reconstruct_10 at success
  obtain ⟨prefix,hprefix,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨iter,hiter,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨reverse,hreverse,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨seed,hseed,success⟩ := FIv_Map.bind_success _ _ _ success
  cases Result.ok.inj hreverse
  cases Result.ok.inj hiter
  exact ⟨prefix,seed,hprefix,hseed,success⟩
#print axioms reached
end AspisR1.FIx_ReconstructSource
end
