import RPv_FJk_CompositionContext
import RPv_FJk_CompositionWideFold
import RPv_FJk_SemanticWideOnRun
import RPv_FJk_PoseidonWideOnRun
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJk_CompositionWideOnRun
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical decoded)
open FIw_CompositionOrigins (SemPub composition)
open FIz_ConcretePack (embed)
def semantic (pub : SemPub) (o : FIw_PublicModel.Openings)
    (s : FIw_PublicModel.Selectors) (j : Fin 24) :=
  R0P.pack4 ConcretePackBasis.basis (fun i=>R0P.SemSource.scalarLaneAt
    (SpendDataMap.mapPublic embed (FIw_PublicModel.ofPublic pub))
    (ValueFamilyFieldTransport.mapOpenings embed (FIw_PublicModel.openings o))
    (fun k=>embed (FIw_PublicModel.selector s k)) (4*j.val+i.val))
def poseidon (pub : SemPub) (o : FIw_PublicModel.Openings)
    (s : FIw_PublicModel.Selectors) (j : Fin 4) :=
  ((R0P.poseidonPackedFamily ConcretePackBasis.basis).residuals
    (SpendDataMap.mapPublic embed (FIw_PublicModel.ofPublic pub))
    (ValueFamilyFieldTransport.mapOpenings embed (FIw_PublicModel.openings o))
    (fun k=>embed (FIw_PublicModel.selector s k))).getD j.val 0
/-- Complete composition VALUE in Wide with the original copy seed retained
for the next link-model refinement. All other families are interpreted. -/
theorem value (pub : SemPub) (claims : Array field.QM31 84#usize) (point : Array field.QM31 10#usize)
    (lambda chi theta comp g h active : field.QM31)
    (c1 : Array field.QM31 16#usize) (mask : Array field.QM31 10#usize)
    (hclaims : canonical claims) (hpoint : canonical point)
    (hlambda : Canon lambda) (hchi : Canon chi) (htheta : Canon theta)
    (bounds : FJa_PublicBounds.Bounds pub)
    (run : composition pub claims point lambda chi theta=ok (.Ok (comp,c1,mask,g,h,active))) :
    ∃ (a a1 a2 : Array field.QM31 16#usize)
      (s : pool_v1.pair_forest_copy_terminal.Selectors)
      (variant : pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1)
      (copy : pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledCopyTerminalV1),
      c1=a ∧ canonical a ∧ canonical a1 ∧ canonical a2 ∧
      pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point=ok s ∧
      pool_v1.pair_forest_semantic_terminal.copy_variant pub.variant=ok variant ∧
      pool_v1.pair_forest_copy_terminal.evaluate_with_selectors a h s lambda chi
        pub.transition.live_snapshot.next_pair_index variant=ok copy ∧
      copy.active=active ∧ Canon copy.residual ∧ Canon active ∧ Canon comp ∧
      embed (decode comp)=ExtractedMaskTerminalHorner.composeGroups (embed (decode theta))
        (embed (decode copy.residual)) (semantic pub ⟨a,a1,a2⟩ s) (poseidon pub ⟨a,a1,a2⟩ s) := by
  obtain ⟨a,a1,a2,s,po,variant,sem,pos,copy,same,ca,ca1,ca2,rs,rsp,rsem,rpo,rv,rc,ra,cr,act,cc,cv⟩ :=
    FJk_CompositionContext.value pub claims point lambda chi theta comp g h active c1 mask
      hclaims hpoint hlambda hchi htheta bounds run
  have sv := FJk_SemanticWideOnRun.value pub ⟨a,a1,a2⟩ s point sem ca ca1 ca2 hpoint bounds rs rsem
  have pv := FJk_PoseidonWideOnRun.value pub ⟨a,a1,a2⟩ point s po pos ca ca1 ca2 hpoint rs rsp rpo
  refine ⟨a,a1,a2,s,variant,copy,same,ca,ca1,ca2,rs,rv,rc,ra,cr,act,cc,?_⟩
  have sv' : (fun i : Fin 24=>embed (decoded sem i))=semantic pub ⟨a,a1,a2⟩ s := by
    funext i
    exact congrFun sv.2 i
  have pv' : (fun i : Fin 4=>embed (decoded pos i))=poseidon pub ⟨a,a1,a2⟩ s := by
    funext i
    exact congrFun pv.2 i
  exact (congrArg embed cv).trans ((FJk_CompositionWideFold.value embed (decode theta) sem pos copy.residual).trans
    (congrArg₂ (ExtractedMaskTerminalHorner.composeGroups (embed (decode theta))
      (embed (decode copy.residual))) sv' pv'))
#print axioms value
end AspisR1.FJk_CompositionWideOnRun
end
