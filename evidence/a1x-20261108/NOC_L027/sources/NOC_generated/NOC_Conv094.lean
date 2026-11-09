import NNV_CurrentGeometry
import NNV_CurrentScan
import NNH_Run5bCurrentPending
import LIBC_AccNew
import LIBC_WeightsNew
set_option autoImplicit false
noncomputable section
namespace AspisR1.NOC_Conv094
open Aeneas Aeneas.Std Result
variable (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)

/-- Converse, canonical scan (op4) on the 57607-byte proof. -/
theorem scan (proof : Slice U8) (width : proof.val.length=57607)
 (h : (NNH_Run5bCurrentShape.current m env err r).op4 proof = .ok (.Ok ())) (env' : RSL.Env) :
 LIBC_CanonicalScan.value (LIB_Carriers.bytes proof) env' = .ok () := by
 rw [NNV_CurrentScan.source m env err r proof width] at h
 unfold LIBC_CanonicalScan.value
 cases hg : LIBC_CanonicalScan.good (LIB_Carriers.bytes proof)
 · rw [hg] at h; simp at h
 · rfl

/-- Converse, geometry (op19). -/
theorem geometry (p : LIB_VCarriers.Prepared) (start stop : Nat) (out : Tx1Q_Carriers.C.G)
 (h : (NNH_Run5bCurrentShape.current m env err r).op19 p.queries (LIBC_Usize.raw start) (LIBC_Usize.raw stop) =
  .ok (.Ok out)) :
 ∃ geo, LIBC_Geometry.value (p,start,stop) env = .ok geo ∧ Tx1Q_PrefixInstall.unGeometry geo = out := by
 rw [NNV_CurrentGeometry.source] at h
 unfold Tx1Q_PrefixInstall.topResult at h
 cases hm : LIBC_Geometry.model (p,start,stop) env with
 | ok reply =>
  rw [hm,bind_tc_ok] at h
  cases reply with
  | Ok g =>
   injection h with h
   injection h with h
   refine ⟨g,?_,h⟩
   unfold LIBC_Geometry.value
   rw [hm]
   rfl
  | Err e => simp at h
 | fail e => rw [hm] at h; simp at h
 | div => rw [hm] at h; simp at h

/-- Converse, accumulator constructor (op20). -/
theorem accNew (out : Tx1Q_Carriers.C.A)
 (h : (NNH_Run5bCurrentShape.current m env err r).op20 .S2 = .ok (.Ok out)) :
 LIBC_AccNew.value env = .ok (LIBC_VStateCarriers.fromAcc (Tx1Q_Carriers.accumulator out)) := by
 have h' : Tx1Q_PrefixInstall.initial env.reservation .S2 = .ok (.Ok out) := h
 have s := Tx1Q_PrefixInstall.initial_success _ _ h'
 unfold LIBC_AccNew.value LIBC_AccNew.model
 rw [s]
 rfl

/-- Converse, pending weights (op18) on the SAME returned accumulator. -/
theorem weightsNew (a : LIB_VCarriers.Acc) (width : a.weights.val.length=64) (out : Tx1Q_Carriers.C.B)
 (h : (NNH_Run5bCurrentShape.current m env err r).op18
   (Tx1Q_Carriers.unAccumulator (LIBC_VStateCarriers.toAcc a)).weights.deref = .ok (.Ok out)) :
 LIBC_WeightsNew.value a env = .ok (Tx1Q_Carriers.pending out) := by
 have size : (LIBC_VStateCarriers.toAcc a).weights.val.length=64 :=
  (LIBC_VStateCarriers.weights_length a).trans width
 have round := congrArg (fun s : AspisR1Stage2.verifier.Accumulator => s.weights.deref)
  (Tx1Q_Carriers.accumulator_roundtrip (LIBC_VStateCarriers.toAcc a))
 change Tx1Q_Carriers.slice Tx1Q_Carriers.k
  (Tx1Q_Carriers.unAccumulator (LIBC_VStateCarriers.toAcc a)).weights.deref =
  (LIBC_VStateCarriers.toAcc a).weights.deref at round
 have h' : Tx1Q_PrefixInstall.newPending env.reservation
   (Tx1Q_Carriers.unAccumulator (LIBC_VStateCarriers.toAcc a)).weights.deref = .ok (.Ok out) := h
 have s := Tx1Q_PrefixInstall.pending_success _ _ _ h'
 rw [round] at s
 have s2 := (Port3_NativePendingInstall.reference_eq _ _ size).symm.trans s
 change LIBC_ResultGraph.value LIBC_WeightsNew.port (.error .Allocation)
  (Port3_PendingInstall.pending env.reservation (LIBC_VStateCarriers.toAcc a).weights.deref) = _
 exact congrArg (LIBC_ResultGraph.value LIBC_WeightsNew.port (.error .Allocation)) s2
#print axioms scan
#print axioms geometry
#print axioms accNew
#print axioms weightsNew
end AspisR1.NOC_Conv094
end
