import Lean
import NFN_PhaseTransport
import NFS_NEV_AccumulateCallees
import NEI_PushRawAssociation
import Port3_NativeRowFrame

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NFS_NEV_PushUse
open Aeneas Aeneas.Std Result NEV_AccumulateCarriers

def fromNEG (b : NEG_PushActual.BatchedWeights) : AspisR1Stage2.verifier.BatchedWeights :=
 ⟨b.raw,b.terms⟩

/-- Reuse the CLOSED NEI/NEG push association on the SAME carrier and inputs.
Only nominal record conversions compose here, preserving every Result tag.
The bounded row-domain obligation remains separately caller-established. -/
theorem association (b : NEV_AccumulateRaw.BatchedWeights) (index : Usize)
    (power : RawQ) (basis : U32) :
    (do let out ← NEV_AccumulateRaw.BatchedWeights.push b index power basis
        ok (toWeights out)) =
      AspisR1.Port3_NativeRowFrame.push (toWeights b) index (toQ power) basis := by
  have base := NEI_PushRawAssociation.push
    (⟨b.raw,b.terms⟩ : NEI_PushRaw.BatchedWeights) index
    (NEV_AccumulateRaw.NEV_Bindings.toPushQ power) basis
  rw [NEG_PushAssociation.source] at base
  have lifted := congrArg (fun result : Result NEG_PushActual.BatchedWeights =>
    do let out ← result;ok (fromNEG out)) base
  simpa only [NEV_AccumulateRaw.BatchedWeights.push,toWeights,fromNEG,
    NEI_PushRawAssociation.toBW,NEI_PushRawAssociation.toPower,
    NEV_AccumulateRaw.NEV_Bindings.toPushQ,toQ,
    AspisR1.Port3_NativeRowFrame.push,AspisR1.Port3_RowsInstall.toBW,
    AspisR1.Port3_RowsInstall.fromBW,AspisR1.Port3_RowsInstall.toK,
    NEG_RowAssociation.toOld,Port26ROW.toK,bind_assoc_eq,bind_tc_ok] using lifted
#print axioms association
end NFS_NEV_PushUse
end

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
