import FJn_TerminalModel
import JGa_TerminalParts
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJn_TerminalPartsNonvacuity
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open FIw_CompositionOrigins (SemPub composition)
open FIz_ConcretePack (embed)
attribute [local irreducible] FJn_TerminalModel.model
/-- Construct an actual terminal tail from its SAME reached composition,
then derive the full model value. This is local conditional non-vacuity,
not an independently assumed terminal success or a full deployed fixture. -/
theorem value (p : SemPub) (claims : Array field.QM31 84#usize)
    (point zc : Array field.QM31 10#usize) (lambda chi theta mu : field.QM31)
    (comp g h active : field.QM31) (c1 : Array field.QM31 16#usize) (mask : Array field.QM31 10#usize)
    (hc : canonical claims) (hp : canonical point) (hz : canonical zc)
    (hl : Canon lambda) (hchi : Canon chi) (ht : Canon theta) (hm : Canon mu)
    (bounds : FJa_PublicBounds.Bounds p)
    (run : composition p claims point lambda chi theta=ok (.Ok (comp,c1,mask,g,h,active))) :
    ∃ out,FIr_TerminalTrace.parts p claims point lambda chi theta zc mu=ok (.Ok (out,c1,mask,g)) ∧
      Canon out ∧ embed (FIv_NativeValue.decode out)=FJn_TerminalModel.model p claims point zc lambda chi theta mu := by
  have cm:=FJn_CompositionModel.value p claims point lambda chi theta comp g h active c1 mask hc hp hl hchi ht bounds run
  have hh:=FIr_H1Canonical.canonical p claims point lambda chi theta comp g h active c1 mask run hc
  obtain ⟨out,called,can⟩:=JGa_TerminalParts.source p claims point zc lambda chi theta mu comp c1 mask g h active
    run hp hz cm.1 hm hh cm.2.1
  exact ⟨out,called,FJn_TerminalModel.value p claims point zc lambda chi theta mu out c1 mask g hc hp hz hl hchi ht hm bounds called⟩
#print axioms value
end AspisR1.FJn_TerminalPartsNonvacuity
end
