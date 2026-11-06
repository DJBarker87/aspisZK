import NLH_CompGathers
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_CompGather3
open Aeneas Aeneas.Std Result FIq_Native NLH_CompositionState NLH_CompGathers
open FIv_NativeArithmetic (NQ)
open NKI_InitialPrefix (Public)
theorem step (pub : Public) (claims : Array NQ 84#usize) (point : Array NQ 10#usize)
 (lambda chi theta : NQ) (p : NKR_TermGatherPoseidon.Packet claims point) (base : State) :
 NLH_CompositionState.step pub claims point lambda chi theta (.gather 3) (stage p base 3)=
 ok (.Ok (stage p base 4)) := by
 unfold NLH_CompositionState.step
 rw [p.gather3,bind_tc_ok]
 rfl
#print axioms step
end AspisR1.NLH_CompGather3
end
