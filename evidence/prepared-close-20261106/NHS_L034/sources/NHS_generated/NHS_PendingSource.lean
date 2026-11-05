import NHS_PendingTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHS_PendingSource
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port3_NativePendingBody
/-- The filled reply and the native iteration windows produce the pending
constructor's FULL successful Result on that SAME raw allocation. No newB
success or whole-pending equality is a premise. -/
theorem returned (reservation : NHS_PendingReservation.Reservation)
 (weights : Slice aspis_core.field.QM31) (raw out : alloc.vec.Vec Row)
 (size : weights.val.length=64)
 (allocation : NHS_PendingReservation.heap reservation (Slice.len weights)
   (Array.repeat 4#usize 0#u64)=ok (.Ok raw))
 (cuts : NHS_PendingTrace.Cuts weights raw 0#usize out) :
 NHS_PendingReservation.source reservation weights=ok (.Ok (verifier.BatchedWeights.mk out 0#usize)) := by
 have loop := NHS_PendingTrace.source weights raw out 0#usize size cuts
 unfold NHS_PendingReservation.source extracted
 dsimp! only
 rw [allocation,bind_tc_ok]
 simp only [Port3_Constructor.core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
 rw [loop,bind_tc_ok]
 rfl

/-- A rejected reservation does not manufacture a loop, record or success. -/
theorem rejected (weights : Slice aspis_core.field.QM31) :
 NHS_PendingReservation.source (.Err ()) weights=ok (.Err .Allocation) := by
 unfold NHS_PendingReservation.source NHS_PendingReservation.heap extracted
 dsimp! only
 rw [Port3_NativePendingInstall.heap_exact]
 rfl

/-- SAME native-initializer packet now supplies the formerly OPEN newB input
of NGC_InitialInvariant.initial. The all-zero64 accumulator domain is derived
by NGC_Initialization.accepted, rather than requested from the query loop. -/
theorem initial (constructors : VTop_Stages.Ops) (reserveA : Bool)
 (reservation : NHS_PendingReservation.Reservation)
 (p : verifier.Prepared) (a : verifier.Accumulator) (raw out : alloc.vec.Vec Row)
 (prepared : NGC_PreparationBoundary.Fields p)
 (newA : (Port3_Constructor.installed constructors reserveA).op12 .S2=ok (.Ok a))
 (allocation : NHS_PendingReservation.heap reservation (Slice.len a.weights.deref)
   (Array.repeat 4#usize 0#u64)=ok (.Ok raw))
 (cuts : NHS_PendingTrace.Cuts a.weights.deref raw 0#usize out) :
 NFS_QueryInvariant.Domain p 0 10 a (verifier.BatchedWeights.mk out 0#usize) ∧ a.next.val=0 := by
 obtain ⟨_,weights,_,_,_⟩ := NGC_Initialization.accepted constructors reserveA a newA
 have size : a.weights.deref.val.length=64 := by change a.weights.val.length=64;rw [weights,List.length_replicate]
 exact NHS_PendingReservation.same_initial constructors reserveA reservation p a _ prepared newA
   (returned reservation a.weights.deref raw out size allocation cuts)
#print axioms returned
#print axioms rejected
#print axioms initial
end AspisR1.NHS_PendingSource
