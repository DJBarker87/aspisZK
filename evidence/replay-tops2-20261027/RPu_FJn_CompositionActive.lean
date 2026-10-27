import RPu_FJn_CompositionCopyOnRun
import RPu_FJn_CopySelectors
import RPu_FJa_BoxedSelAt
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJn_CompositionActive
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (Canon decode)
open FIw_ArrayValue (canonical decoded)
open FIw_CompositionOrigins (SemPub composition)
attribute [local irreducible] R0P.copyLinks R0P.copyActiveLiteral R0P.copyResidual
/-- The complete composition's actual active output at its actual point. -/
theorem value (p : SemPub) (claims : Array field.QM31 84#usize) (point : Array field.QM31 10#usize)
    (lambda chi theta comp g h active : field.QM31)
    (c1 : Array field.QM31 16#usize) (mask : Array field.QM31 10#usize)
    (hc : canonical claims) (hp : canonical point)
    (hlambda : Canon lambda) (hchi : Canon chi) (htheta : Canon theta)
    (bounds : FJa_PublicBounds.Bounds p)
    (run : composition p claims point lambda chi theta=ok (.Ok (comp,c1,mask,g,h,active))) :
    Canon active ∧ decode active=R0P.SemSource.activeAt (decoded point) := by
  obtain ⟨a,a1,a2,s,v,_,boxed,_,_,ca,av,_⟩:=
    FJn_CompositionCopyOnRun.value p claims point lambda chi theta comp g h active c1 mask
      hc hp hlambda hchi htheta bounds run
  change decode active=R0P.copyActiveLiteral (FIw_CopyEndpoint.modelSelectors s) at av
  rw [FJn_CopySelectors.value point s hp boxed,FJa_BoxedSelAt.value point s hp boxed] at av
  exact ⟨ca,av⟩
#print axioms value
end AspisR1.FJn_CompositionActive
end
