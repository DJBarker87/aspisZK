import XRz_FinishMaterialize
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSc_FinishRestore
/-- Exact mutable restoration on the SAME successful materialization. -/
theorem source (a : verifier.Accumulator) (pending : verifier.BatchedWeights)
 (slice finished : Slice aspis_core.field.QM31)
 (restore : Slice aspis_core.field.QM31 → alloc.vec.Vec aspis_core.field.QM31)
 (borrow : lift (alloc.vec.Vec.deref_mut a.weights)=ok (slice,restore))
 (domain : slice.val.length≤pending.raw.val.length)
 (run : verifier.BatchedWeights.finish pending slice=ok finished) :
 (restore finished).val=finished.val ∧ finished.val.length=slice.val.length := by
 have restored := congrArg
  (fun p : Slice aspis_core.field.QM31 ×
   (Slice aspis_core.field.QM31 → alloc.vec.Vec aspis_core.field.QM31) => (p.2 finished).val)
  (Result.ok.inj borrow)
 obtain ⟨out,hout,hlen,_⟩ := XRz_FinishMaterialize.source pending slice domain
 have same := Result.ok.inj (hout.symm.trans run)
 refine ⟨restored.symm,?_⟩
 simpa only [same] using hlen
#print axioms source
end XSc_FinishRestore
