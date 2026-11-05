import NGC_PrestateBridge
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHS_PendingReservation
open Aeneas Aeneas.Std Result AspisR1Stage2
abbrev Reservation := core.result.Result Unit Unit

def flag : Reservation → Bool
 | .Ok _ => true
 | .Err _ => false

def heap (r : Reservation) (n : Usize) (value : Port3_NativePendingBody.Row) :=
 match r with
 | .Ok _ => Port3_NativePendingInstall.heap true n value
 | .Err _ => Port3_NativePendingInstall.heap false n value

def source (r : Reservation) (weights : Slice aspis_core.field.QM31) :=
 Port3_QueryInstall.result (Port3_NativePendingBody.extracted (heap r) weights)

/-- Exact reservation-result adapter. The record r denotes the SAME actual
reservation reply; neither success nor an unrelated Bool is assumed. -/
theorem source_eq (r : Reservation) (weights : Slice aspis_core.field.QM31) :
 source r weights=Port3_NativePendingInstall.source (flag r) weights := by
 cases r <;> rfl

/-- Failure and success are both retained by the initializer adapter. -/
theorem same_initial (base : VTop_Stages.Ops) (reserveA : Bool)
 (r : Reservation) (p : verifier.Prepared) (a : verifier.Accumulator)
 (pending : verifier.BatchedWeights) (prepared : NGC_PreparationBoundary.Fields p)
 (newA : (Port3_Constructor.installed base reserveA).op12 .S2=ok (.Ok a))
 (newB : source r a.weights.deref=ok (.Ok pending)) :
 NFS_QueryInvariant.Domain p 0 10 a pending ∧ a.next.val=0 := by
 apply NGC_InitialInvariant.initial base reserveA (flag r) p a pending prepared newA
 exact (source_eq r a.weights.deref).symm.trans newB
#print axioms source_eq
#print axioms same_initial
end AspisR1.NHS_PendingReservation
