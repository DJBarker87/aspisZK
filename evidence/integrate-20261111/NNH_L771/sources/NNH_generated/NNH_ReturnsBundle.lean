import NNH_Libraries
import NNH_Tx1Returns
import NNH_Stage1RefEval
set_option autoImplicit false
noncomputable section
namespace NNH_ReturnsBundle
open RSL NNH_Libraries
abbrev tx1Value := NNH_Stage1RefEval.value VL P NNH_Tx1Returns.values C
abbrev tx2Value := NNH_Libraries.tx2Value
/-- Complete345 RSL evaluator at the delivered canonical library bundle.
This includes returned Err arms; it does not assert native=model transport. -/
theorem tx1_returns (a : TX1_345.Args) (env : Env) :
 NND_Returned.Returns (TX1_345.Ref VL P C a) env (tx1Value a env) :=
 NNH_Stage1RefEval.returned VL P NNH_Tx1Returns.values C a env
/-- Complete241 RSL evaluator, used only on the selected Ok path by A2. -/
theorem tx2_returns (a : TX2_241.Args) (env : Env) :
 NND_Returned.Returns (TX2_241.Ref L D V0 a) env (tx2Value a env) :=
 NNH_Libraries.tx2_returns a env
#print axioms tx1_returns
#print axioms tx2_returns
end NNH_ReturnsBundle
