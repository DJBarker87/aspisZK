import NKI_InitialPrefix
import NLH_CompositionState
import NLH_TermComposeTail
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_CompVariant
open Aeneas Aeneas.Std Result FIq_Native NLH_CompositionState
open FIv_NativeArithmetic (NQ)
open NKI_InitialPrefix (Public)
theorem source (pub : Public) (claims : Array NQ 84#usize) (point : Array NQ 10#usize)
 (lambda chi theta : NQ) (st : State) :
 step pub claims point lambda chi theta .variant st=
 ok (.Ok {st with copyVariant := NLH_TermComposeTail.variant pub.variant}) := by
 simp only [step,NLH_TermComposeTail.variant_source,bind_tc_ok]
#print axioms source
end AspisR1.NLH_CompVariant
end
