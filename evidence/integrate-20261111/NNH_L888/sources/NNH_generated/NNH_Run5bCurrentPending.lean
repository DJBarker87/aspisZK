import NNH_Run5bCurrentInitial
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_Run5bCurrentPending
open Aeneas Aeneas.Std Result NNH_Libraries NNH_Run5bCurrentShape

theorem source (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
 (a : VL.Acc) (pending : VL.Weights)
 (width : a.weights.val.length=64)
 (called : LIB_VLib.weightsNewValue a env = .ok pending) :
 (current m env err r).op18
  (Tx1Q_Carriers.unAccumulator (LIBC_VStateCarriers.toAcc a)).weights.deref =
 .ok (.Ok (Tx1Q_Carriers.unPending pending)) := by
 change LIBC_ResultGraph.value LIBC_WeightsNew.port (.error .Allocation)
  (LIBC_WeightsNew.model a env) = .ok pending at called
 obtain ⟨reply,model,image⟩ := NNH_Run5bReturnedGraph.ok _ _ _ pending called
 cases reply with
 | Err e => cases image
 | Ok out =>
  have same : out = pending := Except.ok.inj image
  subst out
  change Port3_PendingInstall.pending env.reservation (LIBC_VStateCarriers.toAcc a).weights.deref = _ at model
  have size : (LIBC_VStateCarriers.toAcc a).weights.val.length=64 :=
   (LIBC_VStateCarriers.weights_length a).trans width
  have native : Port3_NativePendingInstall.source env.reservation (LIBC_VStateCarriers.toAcc a).weights.deref =
   .ok (.Ok pending) := (Port3_NativePendingInstall.reference_eq _ _ size).trans model
  have round := congrArg (fun s : AspisR1Stage2.verifier.Accumulator => s.weights.deref)
   (Tx1Q_Carriers.accumulator_roundtrip (LIBC_VStateCarriers.toAcc a))
  change Tx1Q_PrefixInstall.newPending env.reservation
   (Tx1Q_Carriers.unAccumulator (LIBC_VStateCarriers.toAcc a)).weights.deref = _
  unfold Tx1Q_PrefixInstall.newPending
  rw [round,native]
  rfl
#print axioms source
end AspisR1.NNH_Run5bCurrentPending
end
