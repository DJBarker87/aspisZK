import FJn_LaneModel
import FJn_EqualityMap
import FJn_ClaimsModel
import FJn_SelectedValue
import FJn_TerminalPartsValue
import FJn_ActiveOnPoint
import FJn_CompositionModel
import FJn_CompositionActive
import FJn_ActivePointMap
import FJn_NativeCarrierBridge
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJn_TerminalModel
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical decoded)
open FIw_CompositionOrigins (SemPub composition)
open FIz_ConcretePack (embed)
abbrev E:=AspisWideTower.WideExact
/-- Model of the same selected claims, before the original29-byte-row transport. -/
def model (p : SemPub) (claims : Array field.QM31 84#usize) (point zc : Array field.QM31 10#usize)
    (lambda chi theta mu : field.QM31) : E :=
  R0P.SemSource.terminalValue (SpendDataMap.mapPublic embed (FIw_PublicModel.ofPublic p))
    (embed (decode lambda)) (embed (decode chi)) (embed (decode theta)) (embed (decode mu))
    (fun i=>embed (decoded zc i)) ConcretePackBasis.basis
    (fun j l=>embed (FJn_ClaimsModel.claims claims j l)) (fun i=>embed (decoded point i))
attribute [local irreducible] R0P.SemSource.laneAt R0P.SemSource.selAt R0P.SemSource.eqValue
  R0P.SemSource.activeAt FIw_PublicModel.ofPublic FJn_ClaimsModel.openings
/-- Complete original terminal-parts VALUE in Wide, on precisely its actual
selected claims and canonical point. No child value equation is assumed. -/
theorem value (p : SemPub) (claims : Array field.QM31 84#usize)
    (point zc : Array field.QM31 10#usize) (lambda chi theta mu out : field.QM31)
    (c1 : Array field.QM31 16#usize) (mask : Array field.QM31 10#usize) (g : field.QM31)
    (hc : canonical claims) (hp : canonical point) (hz : canonical zc)
    (hlambda : Canon lambda) (hchi : Canon chi) (htheta : Canon theta) (hmu : Canon mu)
    (bounds : FJa_PublicBounds.Bounds p)
    (run : FIr_TerminalTrace.parts p claims point lambda chi theta zc mu=ok (.Ok (out,c1,mask,g))) :
    Canon out ∧ embed (decode out)=model p claims point zc lambda chi theta mu := by
  obtain ⟨comp,h,active,called,hh,finish⟩:=
    FIr_RootRefined.parts p claims point zc lambda chi theta mu out c1 mask g run hc hz hp hmu
  have cm:=FJn_CompositionModel.value p claims point lambda chi theta comp g h active c1 mask
    hc hp hlambda hchi htheta bounds called
  have av:=FJn_CompositionActive.value p claims point lambda chi theta comp g h active c1 mask
    hc hp hlambda hchi htheta bounds called
  have hs:=FJn_SelectedValue.helper p claims point lambda chi theta comp g h active c1 mask called
  have result:=finish cm.1 cm.2.1
  simp only [FJn_NativeCarrierBridge.decode,FJn_NativeCarrierBridge.array] at result
  have ps : (fun j : Fin 10=>FIv_NativeArray.value point j.val)=decoded point :=
    funext (FJk_CopyRowTransport.cell point)
  have zs : (fun j : Fin 10=>FIv_NativeArray.value zc j.val)=decoded zc :=
    funext (FJk_CopyRowTransport.cell zc)
  refine ⟨result.1,?_⟩
  rw [result.2]
  simp only [FIr_TerminalValue.formula,map_add,map_mul,map_pow,map_sub,map_one]
  rw [FJn_EqualityMap.value,ps,zs,cm.2.2,hs,av.2,FJn_ActivePointMap.value]
  unfold model R0P.SemSource.terminalValue FJn_CompositionModel.pub FJn_CompositionModel.openings
    FJn_CompositionModel.selector FJn_ClaimsModel.openings
  change _=R0P.SemSource.eqValue (fun i=>embed (decoded zc i)) (fun i=>embed (decoded point i))*
    (∑ i : Fin 29,(embed (decode theta))^i.val*R0P.SemSource.laneAt
      (SpendDataMap.mapPublic embed (FIw_PublicModel.ofPublic p))
      (embed (decode lambda)) (embed (decode chi)) ConcretePackBasis.basis
      (ValueFamilyFieldTransport.mapOpenings embed (FJn_ClaimsModel.openings claims))
      (embed (FIv_NativeArray.value claims 26)) (R0P.SemSource.selAt (fun i=>embed (decoded point i))) i)+
    embed (decode mu)*embed (FIv_NativeArray.value claims 26)+
    embed (decode mu)*embed (decode mu)*((1-R0P.SemSource.activeAt (fun i=>embed (decoded point i)))*
      embed (FIv_NativeArray.value claims 26))
  ring
#print axioms value
end AspisR1.FJn_TerminalModel
end
