import FJn_ModelInputs
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJn_CompositionSeed
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (Canon decode)
open FIw_ArrayValue (canonical)
open FIz_ConcretePack (embed)
attribute [local irreducible] FIw_PublicModel.ofPublic FIw_PublicModel.openings FIw_PublicModel.selector
  R0P.copyEvaluateWithSelectors
theorem value (p : FIw_PublicModel.Public) (a b c : Array field.QM31 16#usize)
    (h lambda chi : field.QM31) (point : Array field.QM31 10#usize) (s : FIw_PublicModel.Selectors)
    (v : pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1)
    (copy : pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledCopyTerminalV1)
    (ha : canonical a) (hh : Canon h) (hp : canonical point) (hl : Canon lambda) (hc : Canon chi)
    (boxed : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point=ok s)
    (variant : pool_v1.pair_forest_semantic_terminal.copy_variant p.variant=ok v)
    (run : pool_v1.pair_forest_copy_terminal.evaluate_with_selectors a h s lambda chi
      p.transition.live_snapshot.next_pair_index v=ok copy) :
    embed (decode copy.residual)=
      (R0P.copyEvaluateWithSelectors
        (ValueFamilyFieldTransport.mapOpenings embed (FIw_PublicModel.openings ⟨a,b,c⟩)).z
        (embed (decode h)) (R0P.copySelectors (fun i=>embed (FIw_PublicModel.selector s i)))
        (embed (decode lambda)) (embed (decode chi))
        (SpendDataMap.mapPublic embed (FIw_PublicModel.ofPublic p)).nextPairIndex
        (SpendDataMap.mapPublic embed (FIw_PublicModel.ofPublic p)).variant).1 := by
  have cv:=FJn_CopyWide.value a h s lambda chi p.transition.live_snapshot.next_pair_index v copy point
    ha hh hp hl hc boxed run
  have args : (p.transition.live_snapshot.next_pair_index.val,FJk_CopyDescriptor.variant v)=
      ((SpendDataMap.mapPublic embed (FIw_PublicModel.ofPublic p)).nextPairIndex,
       (SpendDataMap.mapPublic embed (FIw_PublicModel.ofPublic p)).variant) :=
    Prod.ext (FJn_ModelInputs.index p) (FJn_ModelInputs.variant p v variant)
  have step:=congrArg₂ (fun (o : Fin 16 → AspisWideTower.WideExact) (nv : Nat×R0P.Variant)=>
    (R0P.copyEvaluateWithSelectors o (embed (decode h))
      (R0P.copySelectors (fun i=>embed (FIw_PublicModel.selector s i)))
      (embed (decode lambda)) (embed (decode chi)) nv.1 nv.2).1)
    (FJn_ModelInputs.z a b c) args
  exact (congrArg Prod.fst cv).trans step
#print axioms value
end AspisR1.FJn_CompositionSeed
end
