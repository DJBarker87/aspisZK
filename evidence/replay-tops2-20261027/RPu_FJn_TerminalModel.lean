import RPu_FJn_LaneModel
import RPu_FJn_EqualityMap
import RPu_FJn_ClaimsModel
import RPu_FJn_SelectedValue
import RPu_FJn_TerminalPartsValue
import RPu_FJn_ActiveOnPoint
import RPu_FJn_CompositionModel
import RPu_FJn_CompositionActive
import RPu_FJn_ActivePointMap
import RPu_FJn_NativeCarrierBridge
import RPu_FJn_TerminalValueBridge
import RPu_FJn_TerminalFormulaModel
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
attribute [local irreducible] model FJn_CompositionModel.pub FJn_CompositionModel.openings
  FJn_CompositionModel.selector FJn_TerminalFormulaModel.openings
/-- Complete original terminal-parts VALUE in Wide on the SAME actual operands. -/
theorem value (p : SemPub) (claims : Array field.QM31 84#usize)
    (point zc : Array field.QM31 10#usize) (lambda chi theta mu out : field.QM31)
    (c1 : Array field.QM31 16#usize) (mask : Array field.QM31 10#usize) (g : field.QM31)
    (hc : canonical claims) (hp : canonical point) (hz : canonical zc)
    (hlambda : Canon lambda) (hchi : Canon chi) (htheta : Canon theta) (hmu : Canon mu)
    (bounds : FJa_PublicBounds.Bounds p)
    (run : FIr_TerminalTrace.parts p claims point lambda chi theta zc mu=ok (.Ok (out,c1,mask,g))) :
    Canon out ∧ embed (decode out)=model p claims point zc lambda chi theta mu := by
  obtain ⟨comp,h,active,called,finish⟩:=
    FJn_TerminalValueBridge.value p claims point zc lambda chi theta mu out c1 mask g hc hp hz hmu run
  have cm:=FJn_CompositionModel.value p claims point lambda chi theta comp g h active c1 mask
    hc hp hlambda hchi htheta bounds called
  have av:=FJn_CompositionActive.value p claims point lambda chi theta comp g h active c1 mask
    hc hp hlambda hchi htheta bounds called
  have hs:=congrArg embed (FJn_SelectedValue.helper p claims point lambda chi theta comp g h active c1 mask called)
  have result:=finish cm.1 cm.2.1
  have activeEq:=(congrArg embed av.2).trans (FJn_ActivePointMap.value embed (decoded point))
  have hc' : embed (decode comp)=∑ i : Fin 29,(embed (decode theta))^i.val*
      R0P.SemSource.laneAt (SpendDataMap.mapPublic embed (FIw_PublicModel.ofPublic p))
        (embed (decode lambda)) (embed (decode chi)) ConcretePackBasis.basis
        (FJn_TerminalFormulaModel.openings (fun j l=>embed (FJn_ClaimsModel.claims claims j l)))
        (embed (decode h)) (R0P.SemSource.selAt (fun i=>embed (decoded point i))) i := by
    have helper:=congrArg (fun hh=>∑ i : Fin 29,(embed (decode theta))^i.val*
      R0P.SemSource.laneAt (FJn_CompositionModel.pub p) (embed (decode lambda)) (embed (decode chi))
        ConcretePackBasis.basis (FJn_CompositionModel.openings claims) hh (FJn_CompositionModel.selector point) i) hs.symm
    have got:=cm.2.2.trans helper
    unfold FJn_CompositionModel.pub FJn_CompositionModel.openings FJn_CompositionModel.selector at got
    unfold FJn_TerminalFormulaModel.openings
    exact got
  have final:=FJn_TerminalFormulaModel.value
    (SpendDataMap.mapPublic embed (FIw_PublicModel.ofPublic p)) (embed (decode lambda)) (embed (decode chi))
    (embed (decode theta)) (embed (decode mu)) (fun i=>embed (decoded zc i)) (fun i=>embed (decoded point i))
    (fun j l=>embed (FJn_ClaimsModel.claims claims j l)) (embed (decode comp)) (embed (decode h))
    (embed (decode active)) hc' hs activeEq
  refine ⟨result.1,result.2.trans ?_⟩
  unfold model
  exact final
#print axioms value
end AspisR1.FJn_TerminalModel
end
