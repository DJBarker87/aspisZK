import NNH_Run5bCurrentShape
import NNH_Run5bReturnedGraph
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_Run5bCurrentInitial
open Aeneas Aeneas.Std Result NNH_Libraries NNH_Run5bCurrentShape
variable (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)

theorem slot : (current m env err r).op20 .S2 = Tx1Q_PrefixInstall.initial env.reservation .S2 := rfl

theorem returned (a : VL.Acc) (called : LIB_VLib.accNewValue () env = .ok a) :
 ∃ native : AspisR1Stage2.verifier.Accumulator,
 Port3_Initial.constructor env.reservation .S2 = .ok (.Ok native) ∧
 a = LIBC_VStateCarriers.fromAcc native ∧
 (current m env err r).op20 .S2 = .ok (.Ok (Tx1Q_Carriers.unAccumulator native)) := by
 change LIBC_ResultGraph.value LIBC_AccNew.port (.error .Allocation) (LIBC_AccNew.model env) = .ok a at called
 obtain ⟨reply,model,image⟩ := NNH_Run5bReturnedGraph.ok _ _ _ a called
 cases reply with
 | Err e => cases image
 | Ok native =>
  change Port3_Initial.constructor env.reservation .S2 = .ok (.Ok native) at model
  have same : a = LIBC_VStateCarriers.fromAcc native := (Except.ok.inj image).symm
  refine ⟨native,model,same,?_⟩
  rw [slot]
  unfold Tx1Q_PrefixInstall.initial
  simp only [Tx1Q_Carriers.variant]
  exact congrArg (Tx1Q_PrefixInstall.topResult Tx1Q_Carriers.unAccumulator) model
#print axioms slot
#print axioms returned
end AspisR1.NNH_Run5bCurrentInitial
end
