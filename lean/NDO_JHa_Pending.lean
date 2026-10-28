import NDO_JGw_PendingFacts
import NDO_JFn_PendingHistory
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_Pending
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open JGr_Geometry
open S7Kani3CallerTrace (PushTrace Sum)
open S7JoinRowsTrace (Progress)

theorem source (a : verifier.Accumulator) (b : verifier.BatchedWeights)
    (initial : installed.op20 .S2=ok (.Ok a))
    (call : installed.op18 a.weights.deref=ok (.Ok b)) :
    let aa := Tx1Q_Carriers.accumulator a
    let bb := Tx1Q_Carriers.pending b
    let old := Port3_PendingInstall.owned aa.weights.deref
    aa.weights.val.length=64 ∧ aa.next=0#usize ∧
      Port4C_QueryArithmetic.CanonE aa.rhs ∧ Port3_FlushInstall.Canonical aa.power ∧
      PushTrace old (Port3_RowsInstall.toBW bb) (S7Kani3CallerTrace.initialSum old) ∧
      Progress 0 0 (Port3_RowsInstall.toBW bb) := by
  dsimp only
  have facts := JGw_InitialFacts.source a initial
  have size : (Tx1Q_Carriers.accumulator a).weights.val.length=64 := by
    rw [facts.1,List.length_replicate]
  rw [JGw_InstalledSlots.pending] at call
  have native := Tx1Q_PrefixInstall.pending_success true a.weights.deref b call
  have reference : Port3_PendingInstall.pending true (Tx1Q_Carriers.accumulator a).weights.deref=
      ok (.Ok (Tx1Q_Carriers.pending b)) := by
    have eq := Port3_NativePendingInstall.reference_eq true (Tx1Q_Carriers.accumulator a).weights.deref size
    exact eq.symm.trans native
  refine ⟨size,facts.2.2.2,?_,?_,Port3_PendingInstall.accepted_trace true _ _ reference,
    Port3_PendingInstall.accepted_progress true _ _ size reference⟩
  · rw [facts.2.1]
    change (0<2147483647 ∧ 0<2147483647 ∧ 0<2147483647 ∧ 0<2147483647) ∧
      (0<2147483647 ∧ 0<2147483647 ∧ 0<2147483647 ∧ 0<2147483647)
    omega
  · rw [facts.2.2.1]
    change 1<2147483647 ∧ 0<2147483647 ∧ 0<2147483647 ∧ 0<2147483647
    omega
#print axioms source
end AspisR1.JHa_Pending
end
