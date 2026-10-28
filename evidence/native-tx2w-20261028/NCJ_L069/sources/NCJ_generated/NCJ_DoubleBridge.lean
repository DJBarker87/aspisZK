import NCJ_ConstructorQM
import NCJ_DoubleAssociation
set_option autoImplicit false
noncomputable section
namespace NCJ_DoubleBridge
open Aeneas Aeneas.Std Result AspisR1 NCJ_ConstructorQM

/-- Same-input constructor result and literal frozen double port, without an
assumed successful constructor/helper output. Native data-flow evidence is
K013/014; native primitive add/sub and field source-to-runtime ports remain
exact lower-unit qualifications rather than new axioms. -/
theorem source (x : Q) (canonical : Canon x) :
    ∃ out,FIn_WeightsExtract.double x=ok out ∧ Canon out ∧
      NCJ_DoubleAssociation.sourcePort (FIo_Install.toQ x)=ok (FIo_Install.toQ out) ∧
      FJc_WeightValues.decode out=2*(FJc_WeightValues.decode x)^2-1 := by
  obtain ⟨out,run,co⟩ := NCJ_ConstructorQM.double x canonical
  have value := FJr_DoubleValue.value x out canonical run
  exact ⟨out,run,co,NCJ_DoubleAssociation.constructor x out run,
    value.2.trans (FJd_LoopReference.double_polynomial _)⟩

#print axioms source
end NCJ_DoubleBridge
