import RPz7_GExq_OuterGoodLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExq_OuterGoodMap
open Aeneas Aeneas.Std Result S2W_Trace S2W_Outer GExq_OuterLower GExq_OuterGoodLaws

theorem mapError_good {A : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (r : core.result.Result A AdapterRw.aspis_r1_cost_probe.verifier.Error) :
    Good hashv (mapError traceEffects.op44 r) := by
  cases r with
  | Ok a => exact pure_good _ _
  | Err e =>
    apply call_bind_good
    · trivial
    · intro out; exact pure_good _ _

#print axioms mapError_good
end AspisR1.GExq_OuterGoodMap
end
