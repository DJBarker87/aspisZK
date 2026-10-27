import FIq_Install
import JFu_CircleExact
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGe_Boundaries
open Aeneas Aeneas.Std Result AspisR1PublicPreparation

/-- All eight fields are the retained source procedures. There is no supplied
success callback or constant-success terminal. -/
def value : FinishModel.Boundaries where
  fromFn := OraclePortStdBuilder.fromFn
  mask := FIp_SemanticArithmetic.mask
  add := FIp_SemanticArithmetic.add
  mul := FIp_SemanticArithmetic.mul
  terminal := FIq_Terminal.terminal
  circle := F3M_CircleSource.source
  unwrapRoot := core.result.Result.unwrap
  claims := ClaimsUnrolledFinish.claims (NP6_StdModel.calls (.Ok ()))

theorem circle : F3M_CircleSource.install value=value := rfl
#print axioms circle
end AspisR1.JGe_Boundaries
end
