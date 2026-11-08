import NMX_R9_StageTwo
import NNH_064Install
set_option autoImplicit false
noncomputable section
namespace NNS_SameConstant
open Aeneas Aeneas.Std AdapterRw

/-- The represented branch's actual 064 interface is a relation, not f064. -/
theorem native_child (ch : NMX_R4_Authentication.Choices) (pub proof ck : Slice U8) :
 (NMX_R9_Children241.original ch).op11
  (NMX_R8_Std241.ops (Classical.ofNonempty : RSL.Env)) pub proof ck () none =
 NMX_R7_VerifierSource241.meaning pub proof ck := rfl

/-- The fallback's selected 064 function, with the exact bytes argument order. -/
theorem fallback_child : NMX_R7_Verify241.verify =
 (fun x env => if fits : LIBB_Tx2Auth.Fits x.1 x.2.1 x.2.2 then
  LIBB_Tx2EnvTrace.observation env
   (LIB_Bytes.fromBytes x.1 fits.1) (LIB_Bytes.fromBytes x.2.1 fits.2.1)
   (LIB_Bytes.fromBytes x.2.2 fits.2.2)
  else ⟨.abort,[]⟩) := rfl

/-- Diagnostic only: a successful compile verifies that rfl does not identify
these functions. It is not a proof of their mathematical inequality. -/
example : True := by
 fail_if_success
  have : NMX_R7_Verify241.verify =
   (fun x env => AspisR1.NNH_064Install.f064 x.1 x.2.1 x.2.2 env) := by rfl
 trivial

#print axioms native_child
#print axioms fallback_child
end NNS_SameConstant
