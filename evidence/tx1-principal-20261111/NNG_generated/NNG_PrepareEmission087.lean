import NMP_PrepareSource
import NNG_PreparedCall087
import NNG_Filled087
import NNG_ExpandSemantic087
import NNG_ExpandValues087
import NNG_WideView087
import NNG_Context137
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_PrepareEmission087
open Aeneas Aeneas.Std Result NMP_prepare NMP_Emitted

def calls (env : RSL.Env) : Calls where
 c0 := NMP_StdMapErr.run
 c1 := NNG_Filled087.call env
 c2 := NNG_WideView087.call
 c3 := NNG_PreparedCall087.call
 c4 := fun _ _=>.ok ()
 c5 := (NNG_Context137.calls env).begin_
 c6 := (NNG_Context137.calls env).parse
 c7 := (NNG_Context137.calls env).finish
 c8 := (NNG_Context137.calls env).mark
 c9 := (NNG_Context137.calls env).publicTranscript
 c10 := NNG_ExpandSemantic087.call
 c11 := NNG_ExpandValues087.call

theorem erasure {H W : Type} (env : RSL.Env) (s : Parent H W) :
 NMT_CallTree.erase (NMP_PrepareSteps.body (calls env) s) = prepare (calls env) s :=
 NMP_PrepareSuffix.emitted (calls env) s
#print axioms erasure
end AspisR1.NNG_PrepareEmission087
