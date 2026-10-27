import XSc_QueryPendingReach
import XRr_Accepted64
import XRu_NewLength
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSc_QueryDestination
/-- The complete finish length domain is derived from these SAME initialization,
query and mutable borrow cuts. It is not a new reserve or canonicality premise. -/
theorem source (proof : Slice U8) (p : verifier.Prepared)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (obs : Option (verifier.Phase → Result Unit)) (geo : verifier.QueryGeometry)
 (end1 : Usize) (initial a : verifier.Accumulator) (pending0 pending : verifier.BatchedWeights)
 (slice : Slice aspis_core.field.QM31)
 (restore : Slice aspis_core.field.QM31 → alloc.vec.Vec aspis_core.field.QM31)
 (hinit : verifier.Accumulator.new .S2=ok (.Ok initial))
 (hnew : verifier.BatchedWeights.new initial.weights.deref=ok (.Ok pending0))
 (hquery : verifier.candidate.query_loop proof p initial g obs geo pending0 end1=ok (.Ok (a,pending)))
 (hborrow : lift (alloc.vec.Vec.deref_mut a.weights)=ok (slice,restore)) :
 slice.val.length=64 ∧ pending.raw.val.length=64 ∧ a.next.val=end1.val := by
 have init := XRr_Initial64.init initial hinit
 have fresh := XRu_NewLength.source initial.weights.deref pending0 hnew
 have path := XSc_QueryPath.source proof p g obs geo end1 (.Ok (initial,pending0)) (.Ok (a,pending)) hquery
 have raw := XSc_QueryPendingReach.reached proof p g obs geo end1 initial pending0 (.Ok (a,pending)) path
 have actual := XRr_Accepted64.source proof p g obs geo end1 initial a pending0 pending hinit hquery
 have same := congrArg Prod.fst (Result.ok.inj hborrow)
 have dest : slice.val.length=a.weights.val.length :=
  congrArg (fun w : Slice aspis_core.field.QM31 => w.val.length) same.symm
 exact ⟨dest.trans actual.2.2.1,raw.trans (fresh.1.trans init.1),actual.2.2.2⟩
#print axioms source
end XSc_QueryDestination
