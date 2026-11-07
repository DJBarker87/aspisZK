import LIBC_ResultGraph
import LIBC_VStateCarriers
import NGC_Initialization
set_option autoImplicit false
noncomputable section
namespace LIBC_AccNew
open Aeneas Aeneas.Std Result AspisR1 RSL
def port : core.result.Result AspisR1Stage2.verifier.Accumulator VTop_Stages.verifier.Error →
 Except LIB_VCarriers.VErr LIB_VCarriers.Acc
 | .Ok a => .ok (LIBC_VStateCarriers.fromAcc a) | .Err e => .error e
def model (env : Env) := Port3_Initial.constructor env.reservation .S2
def child : Child Unit (Except LIB_VCarriers.VErr LIB_VCarriers.Acc) :=
 ⟨fun _ => True,fun _ => LIB_Carriers.resultGraph port model (fun _ => [])⟩
def value (env : Env) := LIBC_ResultGraph.value port (.error .Allocation) (model env)
theorem returns (env : Env) : NND_Returned.Returns (child.law ()) env (value env) :=
 LIBC_ResultGraph.returns _ _ _ _ env
theorem functional : Child.Functional child := by
 intro _ _
 exact LIBC_ResultGraph.functional _ _ _
/-- Fixed emitted constructor leaves and literal S2: no base Ops dictionary
and no reservation-success hypothesis enter the field law. -/
theorem source (env : Env) :
 Port3_Constructor.extracted (Port3_Constructor.leaves env.reservation) .S2 = model env :=
 Port3_Constructor.normalization _ _
theorem graph (env : Env) (o : Obs (Except LIB_VCarriers.VErr LIB_VCarriers.Acc)) :
 child.law () env o ↔ o = LIB_Carriers.resultObs port [] (model env) := Iff.rfl
#print axioms returns
#print axioms functional
#print axioms source
#print axioms graph
end LIBC_AccNew
