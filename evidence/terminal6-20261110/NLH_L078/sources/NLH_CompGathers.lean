import NKI_InitialPrefix
import NLH_CompositionState
import NLH_RustCuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_CompGathers
open Aeneas Aeneas.Std Result FIq_Native NLH_CompositionState
open FIv_NativeArithmetic (NQ)
open NKI_InitialPrefix (Public)
def stage {claims point} (p : NKR_TermGatherPoseidon.Packet claims point) (base : State) (n : Nat) : State :=
 {base with openings :=
  {z := if 1 ≤ n then p.z else base.openings.z,
   succ_z := if 2 ≤ n then p.succ else base.openings.succ_z,
   xor12_z := if 3 ≤ n then p.xor12 else base.openings.xor12_z},
  mask := if 4 ≤ n then p.mask else base.mask}
end AspisR1.NLH_CompGathers
end
