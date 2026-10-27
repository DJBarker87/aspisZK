import RPu_FJn_CopyWide
import RPu_FJn_ClaimsModel
import RPu_FJn_SelAtMap
import RPu_FJa_BoxedSelAt
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJn_ModelInputs
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (decode)
open FIw_ArrayValue (canonical decoded)
open FIz_ConcretePack (embed)
attribute [local irreducible] FIw_PublicModel.ofPublic FIw_PublicModel.openings FIw_PublicModel.selector
/-- A shallow cell transport; no public or selector definition is reduced. -/
theorem z (a b c : Array field.QM31 16#usize) :
    (fun i=>embed (decoded a i))=
      (ValueFamilyFieldTransport.mapOpenings embed (FIw_PublicModel.openings ⟨a,b,c⟩)).z := by
  funext i
  unfold ValueFamilyFieldTransport.mapOpenings FIw_PublicModel.openings
  exact congrArg embed (FJk_CopyRowTransport.cell a i).symm
/-- Original variant conversion agrees with the model public's variant. -/
theorem variant (p : FIw_PublicModel.Public)
    (v : pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1)
    (run : pool_v1.pair_forest_semantic_terminal.copy_variant p.variant=ok v) :
    FJk_CopyDescriptor.variant v=(SpendDataMap.mapPublic embed (FIw_PublicModel.ofPublic p)).variant := by
  cases vv : p.variant <;>
    simp only [pool_v1.pair_forest_semantic_terminal.copy_variant,vv] at run
  all_goals cases Result.ok.inj run
  all_goals simp only [SpendDataMap.mapPublic,FIw_PublicModel.ofPublic,
    FIw_CoefficientTransport.variant,FJk_CopyDescriptor.variant,vv]
theorem index (p : FIw_PublicModel.Public) :
    p.transition.live_snapshot.next_pair_index.val=
      (SpendDataMap.mapPublic embed (FIw_PublicModel.ofPublic p)).nextPairIndex := by
  unfold SpendDataMap.mapPublic FIw_PublicModel.ofPublic
  rfl
theorem selector (point : Array field.QM31 10#usize) (s : FIw_PublicModel.Selectors)
    (hp : canonical point)
    (boxed : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point=ok s) :
    (fun i=>embed (FIw_PublicModel.selector s i))=R0P.SemSource.selAt (fun i=>embed (decoded point i)) := by
  have h:=congrArg (fun (f : R0P.Sel FIv_NativeValue.K)=>fun i=>embed (f i))
    (FJa_BoxedSelAt.value point s hp boxed)
  exact h.trans (FJn_SelAtMap.value embed (decoded point))
#print axioms z
#print axioms variant
#print axioms index
#print axioms selector
end AspisR1.FJn_ModelInputs
end
