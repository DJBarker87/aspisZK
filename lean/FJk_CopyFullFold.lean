import FJk_CopyFold
import JFy_ZeroArrays
import FIx_ArrayMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJk_CopyFullFold
open Aeneas Aeneas.Std Result FIq_Native
open pool_v1.pair_forest_copy_terminal
open FIv_NativeValue (K)
open FIw_ArrayValue (canonical decoded)
def initial : R0P.CopyRowExtension K := ⟨fun _=>0,fun _=>0,fun _=>0,fun _=>0⟩
def model (s : Selectors) (patterns : Array field.QM31 14#usize) (index : U64)
    (v : PoolV1PairForestCompiledVariantV1) : R0P.CopyRowExtension K :=
  R0P.copyLinks.foldl (FJk_CopyStep.step (FIw_CopyEndpoint.modelSelectors s) (decoded patterns)
    index.val (FJk_CopyDescriptor.variant v)) initial
attribute [local irreducible] R0P.copyLinks FJk_CopyStep.step
/-- Complete 136-link VALUE on the original native loop, with actual pattern bytes. -/
theorem value (s : Selectors) (index : U64) (v : PoolV1PairForestCompiledVariantV1)
    (patterns : Array field.QM31 14#usize) (a b c d : Array field.QM31 2#usize)
    (hh : canonical s.high) (hl : canonical s.low) (hp : canonical patterns)
    (run : evaluate_with_selectors_loop s index v patterns
      (Array.repeat 2#usize field.QM31.ZERO) (Array.repeat 2#usize field.QM31.ZERO)
      (Array.repeat 2#usize field.QM31.ZERO) (Array.repeat 2#usize field.QM31.ZERO) 0#usize=ok (a,b,c,d)) :
    canonical a ∧ canonical b ∧ canonical c ∧ canonical d ∧
      FJk_CopyStep.row a b c d=model s patterns index v := by
  have hz := JFy_ZeroArrays.source 2#usize
  have got := FJk_CopyFold.value 136 0#usize s index v patterns _ _ _ _ a b c d rfl hh hl hp hz hz hz hz run
  refine ⟨got.1,got.2.1,got.2.2.1,got.2.2.2.1,?_⟩
  have z : FJk_CopyStep.row (Array.repeat 2#usize field.QM31.ZERO)
      (Array.repeat 2#usize field.QM31.ZERO) (Array.repeat 2#usize field.QM31.ZERO)
      (Array.repeat 2#usize field.QM31.ZERO)=initial := by
    unfold FJk_CopyStep.row
    rw [FIx_ArrayMeaning.decoded_repeat,FIv_NativeValue.zero.2]
    rfl
  have registry := FJk_CopyRegistry.value
  change _=R0P.copyLinks.foldl _ initial
  rw [←registry,List.foldl_map]
  simpa only [show (0#usize).val=0 from rfl,List.drop_zero,z] using got.2.2.2.2
#print axioms value
end AspisR1.FJk_CopyFullFold
end
