import NLH_CompGathers
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_CompGather1
open Aeneas Aeneas.Std Result FIq_Native NLH_CompositionState NLH_CompGathers
open FIv_NativeArithmetic (NQ)
open NKI_InitialPrefix (Public)
theorem step (pub : Public) (claims : Array NQ 84#usize) (point : Array NQ 10#usize)
 (lambda chi theta : NQ) (p : NKR_TermGatherPoseidon.Packet claims point) (base : State) :
 NLH_CompositionState.step pub claims point lambda chi theta (.gather 1) (stage p base 1)=
 ok (.Ok (stage p base 2)) := by
 unfold NLH_CompositionState.step
 rw [p.gather1,bind_tc_ok]
 rfl
#print axioms step
end AspisR1.NLH_CompGather1
end
