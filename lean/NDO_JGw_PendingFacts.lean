import NDO_JGw_InitialFacts
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_PendingFacts
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open JGr_Geometry

theorem source (a : verifier.Accumulator) (b : verifier.BatchedWeights)
    (initial : installed.op20 .S2=ok (.Ok a))
    (call : installed.op18 a.weights.deref=ok (.Ok b)) :
    b.raw.val=(Tx1Q_Carriers.slice Tx1Q_Carriers.k a.weights.deref).val.map Port3_PendingInstall.row ∧
    b.terms=0#usize ∧ b.raw.val.length=64 := by
  have size : (Tx1Q_Carriers.slice Tx1Q_Carriers.k a.weights.deref).val.length=64 := by
    change (Tx1Q_Carriers.accumulator a).weights.val.length=64
    rw [(JGw_InitialFacts.source a initial).1,List.length_replicate]
  rw [JGw_InstalledSlots.pending] at call
  have native := Tx1Q_PrefixInstall.pending_success true a.weights.deref b call
  exact (Port3_NativePendingInstall.accepted_fields true _ _ size native).2
#print axioms source
end AspisR1.JGw_PendingFacts
end
