import NNG_Front087
import NNG_ObservedInput087
import NNG_PrepareErrors087
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_FrontProjection087
open Aeneas Aeneas.Std NMP_prepare
abbrev Args := NNG_PrepareInput087.Args

def verified (a : Args) (env : RSL.Env) (v : verifier.View) (sem : r1_semantic.Verified Unit) : RSL.Verified LIB_Instances.VL :=
 NNG_DProjection136.verified
  (NNG_ProjectionFallback137.representation (NNG_Data137.fallback (NNG_ObservedInput087.child a v) env))
  (NNG_Output137.verified sem)
def port (a : Args) (env : RSL.Env) : NNG_Front087.FrontOut Unit →
 Except LIB_Instances.VL.VErr (RSL.Verified LIB_Instances.VL × LIB_Instances.VL.View)
 | .Err e=>.error (NNG_PrepareErrors087.error e)
 | .Ok (sem,v)=>.ok (verified a env v sem,NNG_PrepareCarriers087.view v)

theorem decoded (a : Args) (env : RSL.Env) (v : verifier.View) (sem : r1_semantic.Verified Unit) :
 NNG_Output137.decode (NNG_ObservedInput087.child a v) env (.Ok sem)=.ok (verified a env v sem) := rfl
#print axioms decoded
end AspisR1.NNG_FrontProjection087
