import NLE_OwnedEncode
set_option autoImplicit false
noncomputable section
namespace NLE_OwnedStep
open Aeneas Aeneas.Std Result AdapterRw NLE_Owned
/-- Exact caller-bound SolanaDigest, SAME three slices, full observer and reply.
The observer's deployed None fact is discharged by the emitted caller body. -/
def tx2 (ops : Ops) (state : State) (publicBytes proof checkpoint : Slice U8)
 (observer : Option (aspis_r1_cost_probe.verifier.Phase → Result Unit)) :
 Run (core.result.Result Unit aspis_r1_cost_probe.verifier.Error) :=
 NJU_Log.record (.tx2 state publicBytes proof checkpoint)
  (ops.op11 (SolanaDigest.Insts.Aspis_coreDigestDigest32 ops) publicBytes proof checkpoint () observer)
theorem tx2_result (ops : Ops) (state : State) (publicBytes proof checkpoint : Slice U8)
 (observer : Option (aspis_r1_cost_probe.verifier.Phase → Result Unit)) :
 (tx2 ops state publicBytes proof checkpoint observer).result =
 ops.op11 (SolanaDigest.Insts.Aspis_coreDigestDigest32 ops) publicBytes proof checkpoint () observer := rfl
theorem release_observer (ops : Ops) : AdapterRw.observer ops = ok none := rfl
#print tx2_result
#print release_observer
#print axioms tx2_result
#print axioms release_observer
end NLE_OwnedStep
