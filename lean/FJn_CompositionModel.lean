import FJn_LaneModel
import FJn_ClaimsModel
import FJn_SelectedValue
import FJn_SelAtMap
import FJa_BoxedSelAt
import FJn_CompositionSeed
import FJn_LaneTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJn_CompositionModel
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical decoded)
open FIw_CompositionOrigins (SemPub composition)
open FIz_ConcretePack (embed)
def pub (p : SemPub) := SpendDataMap.mapPublic embed (FIw_PublicModel.ofPublic p)
def openings (a : Array field.QM31 84#usize) :=
  ValueFamilyFieldTransport.mapOpenings embed (FJn_ClaimsModel.openings a)
def selector (p : Array field.QM31 10#usize) := R0P.SemSource.selAt (fun i=>embed (decoded p i))
attribute [local irreducible] R0P.copyEvaluateWithSelectors R0P.copyActiveLiteral
  R0P.SemSource.laneAt pub openings selector FIw_PublicModel.ofPublic
  FIw_PublicModel.openings FIw_PublicModel.selector
/-- The complete actual composition has the literal29 model lanes on its
SAME selected claims and point. All child model values are derived. -/
theorem value (p : SemPub) (claims : Array field.QM31 84#usize) (point : Array field.QM31 10#usize)
    (lambda chi theta comp g h active : field.QM31)
    (c1 : Array field.QM31 16#usize) (mask : Array field.QM31 10#usize)
    (hc : canonical claims) (hp : canonical point)
    (hlambda : Canon lambda) (hchi : Canon chi) (htheta : Canon theta)
    (bounds : FJa_PublicBounds.Bounds p)
    (run : composition p claims point lambda chi theta=ok (.Ok (comp,c1,mask,g,h,active))) :
    Canon comp ∧ Canon active ∧
    embed (decode comp)=∑ i : Fin 29,(embed (decode theta))^i.val*
      R0P.SemSource.laneAt (pub p) (embed (decode lambda)) (embed (decode chi))
        ConcretePackBasis.basis (openings claims) (embed (FIv_NativeArray.value claims 26)) (selector point) i := by
  obtain ⟨a,a1,a2,s,po,v,sem,pos,prep,middle,copy,it,it1,
    same,r0,r1,r2,rs,rsp,rpo,rsem,rv,rc,rp,rit,rit1,rm,rf,ra⟩:=
    FIw_CompositionOrigins.reached p claims point lambda chi theta comp g h active c1 mask run
  have ca:=FIw_OpeningCanonical.z claims a hc r0
  have ca1:=FIw_OpeningCanonical.succ claims a1 hc r1
  have ca2:=FIw_OpeningCanonical.xor12 claims a2 hc r2
  have cs:=FJa_BoxedCanonical.value point s hp rs
  have hh:=FIr_H1Canonical.canonical p claims point lambda chi theta comp g h active c1 mask run hc
  have sv:=FJk_SemanticWideOnRun.value p ⟨a,a1,a2⟩ s point sem ca ca1 ca2 hp bounds rs rsem
  have pv:=FJk_PoseidonWideOnRun.value p ⟨a,a1,a2⟩ point s po pos ca ca1 ca2 hp rs rsp rpo
  have cc:=FJk_CopyCanonical.value a h s lambda chi p.transition.live_snapshot.next_pair_index v copy ca hh cs.1 cs.2 hlambda hchi rc
  have cv:=FJn_CopyWide.value a h s lambda chi p.transition.live_snapshot.next_pair_index v copy point ca hh hp hlambda hchi rs rc
  have hv:=FJk_HornerValue.value sem pos prep theta copy.residual middle comp it it1 htheta cc.1 sv.1 pv.1 rp rit rit1 rm rf
  have fold:= (congrArg embed hv.2).trans (FJk_CompositionWideFold.value embed (decode theta) sem pos copy.residual)
  have copyV:=FJn_CompositionSeed.value p a a1 a2 h lambda chi point s v copy ca hh hp hlambda hchi rs rv rc
  let wp:=SpendDataMap.mapPublic embed (FIw_PublicModel.ofPublic p)
  let wo:=ValueFamilyFieldTransport.mapOpenings embed (FIw_PublicModel.openings ⟨a,a1,a2⟩)
  let ws : R0P.Sel AspisWideTower.WideExact:=fun i=>embed (FIw_PublicModel.selector s i)
  let sm : Fin 24 → AspisWideTower.WideExact:=fun j=>R0P.pack4 ConcretePackBasis.basis
    (fun i=>R0P.SemSource.scalarLaneAt wp wo ws (4*j.val+i.val))
  let pm : Fin 4 → AspisWideTower.WideExact:=fun j=>
    ((R0P.poseidonPackedFamily ConcretePackBasis.basis).residuals wp wo ws).getD j.val 0
  have se : (fun i : Fin 24=>embed (decoded sem i))=sm := sv.2
  have pe : (fun i : Fin 4=>embed (decoded pos i))=pm := pv.2
  have groups:=congrArg₂ (fun se po=>ExtractedMaskTerminalHorner.composeGroups
    (embed (decode theta)) (embed (decode copy.residual)) se po) se pe
  have seed:=congrArg (fun x=>ExtractedMaskTerminalHorner.composeGroups (embed (decode theta)) x sm pm) copyV
  have full:=fold.trans (groups.trans (seed.trans (FJn_LaneModel.value wp wo ws
    (embed (decode lambda)) (embed (decode chi)) (embed (decode theta)) (embed (decode h)))))
  have os:=congrArg (ValueFamilyFieldTransport.mapOpenings embed) (FJn_ClaimsModel.value claims a a1 a2 r0 r1 r2)
  have ss:=FJn_ModelInputs.selector point s hp rs
  have hs:=congrArg embed (FJn_SelectedValue.helper p claims point lambda chi theta comp g h active c1 mask run)
  have transport:=FJn_LaneTransport.value wp (embed (decode lambda)) (embed (decode chi)) (embed (decode theta))
    wo (ValueFamilyFieldTransport.mapOpenings embed (FJn_ClaimsModel.openings claims))
    (embed (decode h)) (embed (FIv_NativeArray.value claims 26)) ws
    (R0P.SemSource.selAt (fun i=>embed (decoded point i))) os hs ss
  refine ⟨hv.1,ra ▸ cc.2,?_⟩
  unfold pub openings selector
  exact full.trans transport
#print axioms value
end AspisR1.FJn_CompositionModel
end
